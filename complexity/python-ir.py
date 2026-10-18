# Python source -> the same language-neutral IR that from-clike.js produces. Runs inside Pyodide (uses only the stdlib `ast`).
import ast, json

BIN = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/', ast.FloorDiv: '//', ast.Mod: '%', ast.Pow: '**', ast.LShift: '<<', ast.RShift: '>>', ast.BitAnd: '&', ast.BitOr: '|', ast.BitXor: '^', ast.MatMult: '@'}
CMP = {ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=', ast.Eq: '==', ast.NotEq: '!=', ast.Is: '==', ast.IsNot: '!=', ast.In: 'in', ast.NotIn: 'notin'}
MODULES = set()
CLASS_KIND = {'TreeNode': 'tree', 'ListNode': 'node'}


def ann_type(a):
    if a is None:
        return {'k': 'unknown'}
    if isinstance(a, ast.Constant):
        if isinstance(a.value, str):  # forward reference 'TreeNode'
            try:
                return ann_type(ast.parse(a.value, mode='eval').body)
            except Exception:
                return {'k': 'unknown'}
        return {'k': 'null'} if a.value is None else {'k': 'unknown'}
    if isinstance(a, ast.Name):
        return name_type(a.id)
    if isinstance(a, ast.Attribute):
        return name_type(a.attr)
    if isinstance(a, ast.Subscript):
        base = a.value.id if isinstance(a.value, ast.Name) else (a.value.attr if isinstance(a.value, ast.Attribute) else '')
        sl = a.slice
        args = list(sl.elts) if isinstance(sl, ast.Tuple) else [sl]
        a0 = ann_type(args[0]) if args else {'k': 'unknown'}
        a1 = ann_type(args[1]) if len(args) > 1 else {'k': 'unknown'}
        if base in ('List', 'list', 'Sequence', 'Iterable'):
            return {'k': 'list', 'e': a0, 'impl': 'list'}
        if base in ('Dict', 'dict', 'Mapping', 'DefaultDict', 'defaultdict', 'Counter', 'OrderedDict'):
            return {'k': 'map', 'key': a0, 'e': a1}
        if base in ('Set', 'set', 'FrozenSet', 'frozenset'):
            return {'k': 'set', 'e': a0}
        if base in ('Deque', 'deque'):
            return {'k': 'deque', 'e': a0}
        if base in ('Tuple', 'tuple'):
            return {'k': 'tuple'}
        if base == 'Optional':
            return a0
        return {'k': 'unknown'}
    return {'k': 'unknown'}


def name_type(n):
    if n in ('int', 'bool') and n == 'int':
        return {'k': 'int'}
    if n == 'bool':
        return {'k': 'bool'}
    if n == 'float':
        return {'k': 'float'}
    if n == 'str':
        return {'k': 'str'}
    if n in ('list', 'List'):
        return {'k': 'list', 'e': {'k': 'unknown'}, 'impl': 'list'}
    if n in ('dict', 'Dict'):
        return {'k': 'map', 'key': {'k': 'unknown'}, 'e': {'k': 'unknown'}}
    if n in ('set', 'Set'):
        return {'k': 'set', 'e': {'k': 'unknown'}}
    if n in CLASS_KIND:
        return {'k': CLASS_KIND[n], 'cls': n}
    return {'k': 'obj', 'cls': n}


def E(n):
    if n is None:
        return {'t': 'unk'}
    L = getattr(n, 'lineno', 0)
    if isinstance(n, ast.Constant):
        v = n.value
        if v is None:
            return {'t': 'null'}
        if isinstance(v, bool):
            return {'t': 'num', 'v': 1 if v else 0, 'bool': True}
        if isinstance(v, (int, float)):
            return {'t': 'num', 'v': v}
        if isinstance(v, str):
            return {'t': 'lit', 'kind': 'str', 'a': [], 'len': len(v), 's': v}
        return {'t': 'unk'}
    if isinstance(n, ast.Name):
        return {'t': 'id', 'n': n.id}
    if isinstance(n, ast.BinOp):
        return {'t': 'op', 'o': BIN.get(type(n.op), '?'), 'a': [E(n.left), E(n.right)]}
    if isinstance(n, ast.UnaryOp):
        if isinstance(n.op, ast.USub):
            return {'t': 'op', 'o': 'neg', 'a': [E(n.operand)]}
        if isinstance(n.op, ast.Not):
            return {'t': 'op', 'o': '!', 'a': [E(n.operand)]}
        return {'t': 'op', 'o': '~', 'a': [E(n.operand)]}
    if isinstance(n, ast.BoolOp):
        return {'t': 'op', 'o': '&&' if isinstance(n.op, ast.And) else '||', 'a': [E(v) for v in n.values]}
    if isinstance(n, ast.Compare):
        parts = []
        left = n.left
        for op, right in zip(n.ops, n.comparators):
            parts.append({'t': 'op', 'o': CMP.get(type(op), '?'), 'a': [E(left), E(right)]})
            left = right
        return parts[0] if len(parts) == 1 else {'t': 'op', 'o': '&&', 'a': parts}
    if isinstance(n, ast.IfExp):
        return {'t': 'op', 'o': '?:', 'a': [E(n.test), E(n.body), E(n.orelse)]}
    if isinstance(n, ast.Call):
        a = [E(x) for x in n.args] + [E(k.value) for k in n.keywords]
        f = n.func
        if isinstance(f, ast.Name):
            return {'t': 'call', 'fn': f.id, 'a': a, 'line': L, 'kw': [k.arg for k in n.keywords]}
        if isinstance(f, ast.Attribute):
            if isinstance(f.value, ast.Name) and f.value.id in MODULES:
                return {'t': 'call', 'fn': f.value.id + '.' + f.attr, 'a': a, 'line': L, 'kw': [k.arg for k in n.keywords]}
            return {'t': 'call', 'recv': E(f.value), 'm': f.attr, 'a': a, 'line': L, 'kw': [k.arg for k in n.keywords]}
        return {'t': 'call', 'fn': '?', 'a': a, 'line': L, 'dynamic': True}
    if isinstance(n, ast.Subscript):
        sl = n.slice
        if isinstance(sl, ast.Slice):
            return {'t': 'slice', 'o': E(n.value), 'lo': E(sl.lower) if sl.lower else None, 'hi': E(sl.upper) if sl.upper else None, 'step': E(sl.step) if sl.step else None}
        return {'t': 'idx', 'o': E(n.value), 'i': E(sl)}
    if isinstance(n, ast.Attribute):
        return {'t': 'attr', 'o': E(n.value), 'n': n.attr}
    if isinstance(n, (ast.List, ast.Tuple, ast.Set)):
        kind = 'list' if isinstance(n, ast.List) else 'tuple' if isinstance(n, ast.Tuple) else 'set'
        return {'t': 'lit', 'kind': kind, 'a': [E(x) for x in n.elts]}
    if isinstance(n, ast.Dict):
        return {'t': 'lit', 'kind': 'dict', 'a': [E(x) for x in n.values]}
    if isinstance(n, (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)):
        kind = 'list' if isinstance(n, ast.ListComp) else 'set' if isinstance(n, ast.SetComp) else 'dict' if isinstance(n, ast.DictComp) else 'gen'
        gens = []
        conds = []
        for g in n.generators:
            gens.append({'vars': target_names(g.target), 'iter': iter_E(g.iter)})
            conds += [E(c) for c in g.ifs]
        elt = E(n.value) if isinstance(n, ast.DictComp) else E(n.elt)
        return {'t': 'comp', 'kind': kind, 'gens': gens, 'conds': conds, 'elt': elt, 'line': L}
    if isinstance(n, ast.Lambda):
        return {'t': 'lambda', 'body': [{'s': 'return', 'v': E(n.body), 'line': L}]}
    if isinstance(n, ast.JoinedStr):
        return {'t': 'op', 'o': 'fstr', 'a': [E(v.value) for v in n.values if isinstance(v, ast.FormattedValue)]}
    if isinstance(n, ast.NamedExpr):
        return {'t': 'assign', 'op': '=', 'target': E(n.target), 'v': E(n.value)}
    if isinstance(n, ast.Starred):
        return {'t': 'op', 'o': 'star', 'a': [E(n.value)]}
    return {'t': 'unk', 'note': type(n).__name__}


def iter_E(n):
    """for-loop iterable: range(...) keeps its arguments, enumerate/zip/reversed/sorted are unwrapped by the analyzer."""
    return E(n)


def target_names(t):
    if isinstance(t, ast.Name):
        return [t.id]
    if isinstance(t, (ast.Tuple, ast.List)):
        out = []
        for x in t.elts:
            out += target_names(x)
        return out
    return ['_']


def S(stmts):
    out = []
    for n in stmts:
        out += S1(n)
    return out


def S1(n):
    L = getattr(n, 'lineno', 0)
    if isinstance(n, ast.Expr):
        if isinstance(n.value, ast.Constant):
            return []
        return [{'s': 'expr', 'e': E(n.value), 'line': L}]
    if isinstance(n, ast.Assign):
        v = E(n.value)
        out = []
        for t in n.targets:
            out.append({'s': 'assign', 'op': '=', 'target': tgt(t), 'v': v, 'line': L, 'first': isinstance(t, ast.Name)})
        return out
    if isinstance(n, ast.AnnAssign):
        if n.value is None:
            return []
        return [{'s': 'assign', 'op': '=', 'target': tgt(n.target), 'v': E(n.value), 'line': L, 'first': True, 'ann': ann_type(n.annotation)}]
    if isinstance(n, ast.AugAssign):
        return [{'s': 'assign', 'op': BIN.get(type(n.op), '?') + '=', 'target': tgt(n.target), 'v': E(n.value), 'line': L}]
    if isinstance(n, ast.If):
        return [{'s': 'if', 'cond': E(n.test), 'then': S(n.body), 'else': S(n.orelse), 'line': L}]
    if isinstance(n, ast.While):
        return [{'s': 'while', 'cond': E(n.test), 'body': S(n.body), 'line': L, 'orelse': bool(n.orelse)}]
    if isinstance(n, ast.For):
        it = n.iter
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == 'range' and 1 <= len(it.args) <= 3 and not it.keywords:
            a = [E(x) for x in it.args]
            lo, hi, step = (None, a[0], None) if len(a) == 1 else (a[0], a[1], a[2] if len(a) == 3 else None)
            return [{'s': 'for', 'mode': 'range', 'vars': target_names(n.target), 'lo': lo, 'hi': hi, 'step': step, 'body': S(n.body), 'line': L}]
        return [{'s': 'for', 'mode': 'each', 'vars': target_names(n.target), 'iter': E(it), 'body': S(n.body), 'line': L}]
    if isinstance(n, ast.Return):
        return [{'s': 'return', 'v': E(n.value) if n.value else None, 'line': L}]
    if isinstance(n, ast.Break):
        return [{'s': 'break', 'line': L}]
    if isinstance(n, ast.Continue):
        return [{'s': 'continue', 'line': L}]
    if isinstance(n, (ast.Pass, ast.Global, ast.Nonlocal)):
        return []
    if isinstance(n, (ast.Import, ast.ImportFrom)):
        if isinstance(n, ast.Import):
            for a in n.names:
                MODULES.add((a.asname or a.name).split('.')[0])
        return []
    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return [{'s': 'def', 'fn': FUNC(n, None), 'line': L}]
    if isinstance(n, ast.Try):
        return [{'s': 'try', 'body': S(n.body), 'handlers': [S(h.body) for h in n.handlers], 'fin': S(n.finalbody) + S(n.orelse), 'line': L}]
    if isinstance(n, ast.With):
        return S(n.body)
    if isinstance(n, ast.Raise):
        return [{'s': 'throw', 'line': L}]
    if isinstance(n, ast.Assert):
        return [{'s': 'expr', 'e': E(n.test), 'line': L}]
    if isinstance(n, ast.Delete):
        return [{'s': 'del', 'target': tgt(t), 'line': L} for t in n.targets]
    if isinstance(n, ast.ClassDef):
        return []
    return [{'s': 'expr', 'e': {'t': 'unk', 'note': type(n).__name__}, 'line': L}]


def tgt(t):
    if isinstance(t, (ast.Tuple, ast.List)):
        return {'t': 'tuple', 'a': [tgt(x) for x in t.elts]}
    return E(t)


def FUNC(f, cls):
    args = f.args
    params = []
    allargs = list(args.posonlyargs) + list(args.args) + list(args.kwonlyargs)
    for a in allargs:
        if a.arg in ('self', 'cls'):
            continue
        params.append({'n': a.arg, 'ty': ann_type(a.annotation)})
    decos = []
    for d in f.decorator_list:
        x = d.func if isinstance(d, ast.Call) else d
        decos.append(x.id if isinstance(x, ast.Name) else (x.attr if isinstance(x, ast.Attribute) else '?'))
    return {'name': f.name, 'cls': cls, 'line': f.lineno, 'endLine': getattr(f, 'end_lineno', f.lineno), 'params': params, 'body': S(f.body), 'decorators': decos, 'ret': ann_type(f.returns)}


def build_ir(code):
    MODULES.clear()
    try:
        tree = ast.parse(code)
    except SyntaxError as e:
        return json.dumps({'error': 'SyntaxError: %s (line %s)' % (e.msg, e.lineno)})
    # `from x import y` makes y a plain name; `import x` makes x a module
    for n in ast.walk(tree):
        if isinstance(n, ast.Import):
            for a in n.names:
                MODULES.add((a.asname or a.name).split('.')[0])
    funcs = []
    classes = {}
    for n in tree.body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            funcs.append(FUNC(n, None))
        elif isinstance(n, ast.ClassDef):
            fields = []
            for m in n.body:
                if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    funcs.append(FUNC(m, n.name))
                    if m.name == '__init__':
                        for s in ast.walk(m):
                            if isinstance(s, ast.Assign):
                                for t in s.targets:
                                    if isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name) and t.value.id == 'self':
                                        fields.append(t.attr)
            classes[n.name] = {'name': n.name, 'fields': [{'n': x, 'ty': {'k': 'unknown'}} for x in fields]}
            if 'left' in fields or 'right' in fields:
                CLASS_KIND[n.name] = 'tree'
            elif 'next' in fields:
                CLASS_KIND[n.name] = 'node'
    return json.dumps({'lang': 'python', 'funcs': funcs, 'classes': classes, 'classKinds': CLASS_KIND})
