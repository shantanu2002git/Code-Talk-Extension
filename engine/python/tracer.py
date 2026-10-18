# Code Talk Python tracer. Runs inside Pyodide (real CPython). It executes the user's code for real under
# sys.settrace and records the genuine state before every line - nothing is simulated.
import sys, json, time, ast, io, types, inspect, collections, math, traceback

USER_FILE = "<user>"
CAP = 120

PRELUDE = '''
class TreeNode:
    def __init__(self, val=0, left=None, right=None):
        self.val = val
        self.left = left
        self.right = right

class ListNode:
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next
'''


def _is_node(v):
    d = getattr(v, "__dict__", None)
    if not isinstance(d, dict):
        return None
    if ("val" in d or "data" in d or "key" in d or "value" in d) and ("left" in d or "right" in d):
        return "TreeNode"
    if ("val" in d or "data" in d or "key" in d or "value" in d) and "next" in d and "left" not in d:
        return "ListNode"
    return None


def _valname(d):
    for k in ("val", "data", "key", "value"):
        if k in d:
            return k
    return None


def snap(v, heap, depth=0, seen=None):
    if v is None or isinstance(v, bool):
        return v
    if isinstance(v, int):
        return v if abs(v) <= 9007199254740991 else str(v)
    if isinstance(v, float):
        if v != v or v in (float("inf"), float("-inf")):
            return str(v)
        return {"$": "dbl", "v": v} if v.is_integer() and abs(v) < 1e15 else v
    if isinstance(v, str):
        return v if len(v) <= 200 else v[:200] + "…"
    if depth > 6:
        return {"$": "unk", "s": "…"}
    if seen is None:
        seen = set()
    kind = _is_node(v)
    if kind:
        key = "n%d" % id(v)
        if key not in heap and len(heap) < 400:
            heap[key] = {"k": kind}
            rec = heap[key]
            d = v.__dict__
            rec["val"] = snap(d.get(_valname(d)), heap, depth + 1, seen)
            for nm in ("next", "left", "right"):
                if nm in d:
                    t = d[nm]
                    rec[nm] = ("n%d" % id(t)) if _is_node(t) else None
                    if _is_node(t):
                        snap(t, heap, depth + 1, seen)
        return {"$": "ref", "a": key, "k": kind}
    vid = id(v)
    if vid in seen:
        return {"$": "cycle"}
    s2 = seen | {vid}
    if isinstance(v, (list,)):
        out = [snap(x, heap, depth + 1, s2) for x in v[:CAP]]
        return {"$": "trunc", "n": len(v), "e": out} if len(v) > CAP else out
    if isinstance(v, tuple):
        return {"$": "tuple", "e": [snap(x, heap, depth + 1, s2) for x in v[:CAP]]}
    if isinstance(v, collections.deque):
        return {"$": "deque", "e": [snap(x, heap, depth + 1, s2) for x in list(v)[:CAP]], "n": len(v)}
    if isinstance(v, dict):
        items = list(v.items())[:CAP]
        return {"$": "map", "e": [[snap(k, heap, depth + 1, s2), snap(x, heap, depth + 1, s2)] for k, x in items], "n": len(v)}
    if isinstance(v, (set, frozenset)):
        try:
            items = sorted(v)
        except Exception:
            items = list(v)
        return {"$": "set", "e": [snap(x, heap, depth + 1, s2) for x in items[:CAP]], "n": len(v)}
    if isinstance(v, (types.FunctionType, types.BuiltinFunctionType, types.MethodType, type, types.ModuleType)):
        return {"$": "unk", "s": getattr(v, "__name__", "function")}
    d = getattr(v, "__dict__", None)
    if isinstance(d, dict):
        f = {}
        for i, (k, x) in enumerate(d.items()):
            if i >= 20:
                break
            f[k] = snap(x, heap, depth + 1, s2)
        return {"$": "obj", "t": type(v).__name__, "f": f}
    try:
        return {"$": "unk", "s": repr(v)[:60]}
    except Exception:
        return {"$": "unk", "s": type(v).__name__}


def to_plain(v, depth=0):
    if depth > 12:
        return None
    if v is None or isinstance(v, (bool, str)):
        return v
    if isinstance(v, int):
        return v if abs(v) <= 9007199254740991 else str(v)
    if isinstance(v, float):
        return v if v == v and v not in (float("inf"), float("-inf")) else str(v)
    kind = _is_node(v)
    if kind == "ListNode":
        out, n, g = [], v, 0
        while n is not None and g < 10000:
            d = n.__dict__
            out.append(to_plain(d.get(_valname(d)), depth + 1))
            n = d.get("next")
            g += 1
        return out
    if kind == "TreeNode":
        out, q = [], [v]
        while q and len(out) < 5000:
            n = q.pop(0)
            if n is None:
                out.append(None)
                continue
            d = n.__dict__
            out.append(to_plain(d.get(_valname(d)), depth + 1))
            q.append(d.get("left"))
            q.append(d.get("right"))
        while out and out[-1] is None:
            out.pop()
        return out
    if isinstance(v, (list, tuple, collections.deque)):
        return [to_plain(x, depth + 1) for x in v]
    if isinstance(v, (set, frozenset)):
        try:
            return [to_plain(x, depth + 1) for x in sorted(v)]
        except Exception:
            return [to_plain(x, depth + 1) for x in v]
    if isinstance(v, dict):
        return {str(k): to_plain(x, depth + 1) for k, x in v.items()}
    d = getattr(v, "__dict__", None)
    if isinstance(d, dict):
        return {k: to_plain(x, depth + 1) for k, x in d.items()}
    return repr(v)


def build_tree(arr):
    if not arr or arr[0] is None:
        return None
    TreeNode = _ns["TreeNode"]
    root = TreeNode(arr[0])
    q = collections.deque([root])
    i = 1
    while q and i < len(arr):
        n = q.popleft()
        if i < len(arr) and arr[i] is not None:
            n.left = TreeNode(arr[i])
            q.append(n.left)
        i += 1
        if i < len(arr) and arr[i] is not None:
            n.right = TreeNode(arr[i])
            q.append(n.right)
        i += 1
    return root


def build_list(arr):
    ListNode = _ns["ListNode"]
    head = tail = None
    for x in arr or []:
        n = ListNode(x)
        if head is None:
            head = tail = n
        else:
            tail.next = n
            tail = n
    return head


def find_node(root, val):
    seen, st = set(), [root]
    while st:
        n = st.pop()
        if n is None or id(n) in seen:
            continue
        seen.add(id(n))
        d = n.__dict__
        if d.get(_valname(d)) == val:
            return n
        for k in ("right", "left", "next"):
            if d.get(k) is not None:
                st.append(d[k])
    return None


_ns = {}


def _ann_kind(ann, name, code):
    s = ann if isinstance(ann, str) else str(ann)
    if "TreeNode" in s:
        return "trees" if ("List[" in s or "list[" in s or "typing.List" in s) else "tree"
    if "ListNode" in s:
        return "list" if "List[" not in s and "list[" not in s and "typing.List" not in s else "lists"
    if s in ("inspect._empty", "<class 'inspect._empty'>") or ann is inspect.Parameter.empty:
        if (".left" in code or ".right" in code) and name in ("root", "tree", "node", "p", "q", "root1", "root2", "t", "s", "subRoot", "r"):
            return "tree"
        if ".next" in code and name in ("head", "l1", "l2", "list1", "list2", "node", "h", "headA", "headB"):
            return "list"
    return None


def _convert(v, kind, first_tree):
    if kind == "tree":
        if isinstance(v, int) and first_tree is not None:
            return find_node(first_tree, v)
        return build_tree(v) if v is not None else None
    if kind == "list":
        return build_list(v) if v is not None else None
    if kind == "trees":
        return [build_tree(x) for x in v]
    if kind == "lists":
        return [build_list(x) for x in v]
    return v


def detect_entries(code):
    tree = ast.parse(code)
    funcs = []
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            for b in node.body:
                if isinstance(b, (ast.FunctionDef, ast.AsyncFunctionDef)) and not b.name.startswith("_"):
                    funcs.append((b, node.name))
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs.append((node, None))
    called = {}
    for f, _ in funcs:
        for n in ast.walk(f):
            if isinstance(n, ast.Call):
                fn = n.func
                nm = fn.id if isinstance(fn, ast.Name) else fn.attr if isinstance(fn, ast.Attribute) else None
                if nm:
                    called.setdefault(nm, set()).add(f.name)
    out = []
    for f, cls in funcs:
        params = [a.arg for a in f.args.args if a.arg not in ("self", "cls")]
        score = 0
        if not (called.get(f.name, set()) - {f.name}):
            score += 10
        if cls == "Solution":
            score += 5
        score -= f.lineno / 10000
        out.append({"name": f.name, "cls": cls, "params": [{"name": p, "type": ""} for p in params], "line": f.lineno, "endLine": getattr(f, "end_lineno", f.lineno), "score": score})
    out.sort(key=lambda x: -x["score"])
    for o in out:
        del o["score"]
    return out


class _Stop(Exception):
    pass


def run_trace(code, args_json, entry, opts_json):
    opts = json.loads(opts_json)
    args = json.loads(args_json)
    max_steps = opts.get("maxSteps", 3000)
    max_events = opts.get("maxEvents", 4000000)
    time_limit = opts.get("timeMs", 9000) / 1000.0
    out = {"ok": False, "steps": [], "stdout": "", "warnings": [], "truncated": False, "error": None, "result": None}
    try:
        cands = detect_entries(code)
    except SyntaxError as e:
        out["error"] = {"type": "SyntaxError", "message": "%s" % (e.msg,), "line": e.lineno or 1, "kind": "syntax"}
        return json.dumps(out)
    out["candidates"] = cands
    ns = {"__name__": "__usercode__", "__builtins__": __builtins__}
    exec("from typing import *\nfrom collections import *\nimport collections, heapq, bisect, math, itertools, functools, re, string, sys\nfrom functools import *\nfrom itertools import *\nfrom heapq import *\nfrom bisect import *\nfrom math import *", ns)
    _ns.clear()
    _ns.update(ns)
    exec(PRELUDE, ns)
    pre_names = set(ns.keys())
    try:
        compiled = compile(code, USER_FILE, "exec")
        exec(compiled, ns)
    except SyntaxError as e:
        out["error"] = {"type": "SyntaxError", "message": e.msg, "line": e.lineno or 1, "kind": "syntax"}
        return json.dumps(out)
    except Exception as e:
        tb = traceback.extract_tb(e.__traceback__)
        ln = [t.lineno for t in tb if t.filename == USER_FILE]
        out["error"] = {"type": type(e).__name__, "message": str(e), "line": ln[-1] if ln else 1, "kind": "runtime"}
        return json.dumps(out)
    _ns.update(ns)
    # ---- locate entry
    fn = None
    inst = None
    if not entry:
        fit = [c for c in cands if len(c["params"]) == len(args)]
        pick = (fit or cands or [None])[0]
        entry = pick["name"] if pick else None
    pick = next((c for c in cands if c["name"] == entry), None)
    if entry is None or pick is None:
        out["error"] = {"type": "NoEntry", "message": "Could not find a function to run in this code.", "line": 1, "kind": "runtime"}
        return json.dumps(out)
    out["entry"] = entry
    try:
        if pick["cls"]:
            inst = ns[pick["cls"]]()
            fn = getattr(inst, entry)
        else:
            fn = ns[entry]
    except Exception as e:
        out["error"] = {"type": type(e).__name__, "message": "Could not create %s(): %s" % (pick["cls"], e), "line": pick["line"], "kind": "runtime"}
        return json.dumps(out)
    sig = inspect.signature(fn)
    params = list(sig.parameters.values())
    out["entrySig"] = {"name": entry, "params": [{"name": p.name, "type": ("" if p.annotation is inspect.Parameter.empty else str(p.annotation))} for p in params], "ret": ""}
    if len(params) != len(args):
        out["error"] = {"type": "ArgumentError", "message": "%s() takes %d argument(s) but the input has %d" % (entry, len(params), len(args)), "line": pick["line"], "kind": "runtime"}
        return json.dumps(out)
    first_tree = None
    call_args = []
    for p, a in zip(params, args):
        kind = _ann_kind(p.annotation, p.name, code)
        if kind == "tree" and not isinstance(a, int):
            val = _convert(a, kind, None)
            first_tree = first_tree or val
        else:
            val = _convert(a, kind, first_tree)
        call_args.append(val)
    # ---- tracing
    steps = out["steps"]
    state = {"fid": -1, "events": 0, "stop": False, "t0": time.monotonic(), "lastout": 0}
    frames = {}
    buf = io.StringIO()
    skip_names = {"<listcomp>", "<genexpr>", "<dictcomp>", "<setcomp>", "<lambda>"}
    user_defs = set(k for k in ns if k not in pre_names)

    def visible(frame):
        res = {}
        for k, v in frame.f_locals.items():
            if k.startswith("__") or k in ("self", "cls"):
                continue
            if isinstance(v, (types.FunctionType, types.BuiltinFunctionType, types.ModuleType, type, types.MethodType)):
                continue
            res[k] = v
        return res

    def members_of(frame):
        m = {}
        s = frame.f_locals.get("self")
        if s is not None and isinstance(getattr(s, "__dict__", None), dict) and not _is_node(s):
            for k, v in s.__dict__.items():
                if not isinstance(v, (types.FunctionType, types.MethodType)):
                    m[k] = v
        for k in user_defs:
            v = ns.get(k)
            if isinstance(v, (types.FunctionType, types.BuiltinFunctionType, types.ModuleType, type, types.MethodType)):
                continue
            if k.startswith("__") or k.isupper() and isinstance(v, int):
                continue
            m[k] = v
        return m

    def record(frame, ev, ret=None, has_ret=False):
        if len(steps) >= max_steps:
            out["truncated"] = True
            return
        info = frames.get(id(frame))
        if not info:
            return
        heap = {}
        vars_ = {k: snap(v, heap) for k, v in visible(frame).items()}
        st = {"i": len(steps), "line": frame.f_lineno, "fn": frame.f_code.co_name, "depth": info[1], "fid": info[0], "pfid": info[2], "ev": ev, "vars": vars_}
        mem = members_of(frame)
        if mem:
            st["members"] = {k: snap(v, heap) for k, v in mem.items()}
        if heap:
            st["heap"] = heap
        if has_ret:
            st["ret"] = snap(ret, heap)
        txt = buf.getvalue()
        if len(txt) > state["lastout"]:
            st["out"] = txt[state["lastout"]:]
            state["lastout"] = len(txt)
        steps.append(st)

    def tracer(frame, event, arg):
        if frame.f_code.co_filename != USER_FILE:
            return None
        name = frame.f_code.co_name
        if name in skip_names or name == "<module>":
            return None
        if frame.f_code.co_flags & 0x20 or frame.f_code.co_flags & 0x80:  # generator / coroutine
            return None
        state["events"] += 1
        if state["events"] > max_events:
            raise _Stop("The program ran for too many operations — it probably contains an infinite loop (or the input is too large for the visualizer).")
        if state["events"] % 2000 == 0 and time.monotonic() - state["t0"] > time_limit:
            raise _Stop("The program took too long to run in the visualizer (possible infinite loop).")
        if event == "call":
            parent = frame.f_back
            pf = -1
            depth = 0
            while parent is not None:
                pi = frames.get(id(parent))
                if pi:
                    pf, depth = pi[0], pi[1] + 1
                    break
                parent = parent.f_back
            state["fid"] += 1
            frames[id(frame)] = (state["fid"], depth, pf)
            return tracer
        if event == "line":
            record(frame, "line")
        elif event == "return":
            record(frame, "return", arg, True)
            frames.pop(id(frame), None)
        return tracer

    old_stdout = sys.stdout
    old_limit = sys.getrecursionlimit()
    sys.stdout = buf
    sys.setrecursionlimit(opts.get("recursion", 700))
    err = None
    result = None
    try:
        sys.settrace(tracer)
        try:
            result = fn(*call_args)
        finally:
            sys.settrace(None)
    except _Stop as e:
        err = {"type": "Limit", "message": str(e), "line": 0, "kind": "limit"}
    except RecursionError:
        err = {"type": "RecursionError", "message": "Maximum recursion depth exceeded — the recursion never reaches its base case (or the input is too deep for the visualizer).", "line": 0, "kind": "runtime"}
    except BaseException as e:
        err = {"type": type(e).__name__, "message": str(e) or type(e).__name__, "line": 0, "kind": "runtime"}
        err["_tb"] = e.__traceback__
    finally:
        sys.stdout = old_stdout
        sys.setrecursionlimit(old_limit)
    if err is not None:
        tb = err.pop("_tb", None)
        if tb is not None:
            lines = [t.lineno for t in traceback.extract_tb(tb) if t.filename == USER_FILE]
            if lines:
                err["line"] = lines[-1]
        if not err["line"] and steps:
            err["line"] = steps[-1]["line"]
        last = steps[-1] if steps else None
        out["error"] = err
        # final state at the failing line: take the last recorded frame state
        if last and len(steps) < max_steps + 1:
            es = dict(last)
            es["i"] = len(steps)
            es["ev"] = "error"
            es["line"] = err["line"] or last["line"]
            es["message"] = err["message"]
            es.pop("ret", None)
            es.pop("out", None)
            steps.append(es)
    else:
        out["ok"] = True
        out["result"] = to_plain(result)
        out["argsAfter"] = [to_plain(a) for a in call_args]
    txt = buf.getvalue()
    out["stdout"] = txt[-20000:]
    out["totalCalls"] = state["fid"] + 1
    out["warnings"] = []
    out["events"] = state["events"]
    return json.dumps(out)
