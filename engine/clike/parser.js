// Recursive-descent parser for the subset of C++ and Java that LeetCode / GeeksforGeeks solutions use.
// Produces a plain-object AST. Every node carries the 1-based source line it starts on, and blocks also carry
// the line of their closing brace, so the tracer can point at real lines.
import { lex, LexError } from './lexer.js';

export class ParseError extends Error {
  constructor(message, line) { super(message); this.line = line; this.kind = 'syntax'; }
}

const PRIMS = new Set(['int', 'long', 'short', 'char', 'bool', 'boolean', 'byte', 'float', 'double', 'void', 'unsigned', 'signed', 'auto', 'var', 'wchar_t', 'size_t', 'int8_t', 'int16_t', 'int32_t', 'int64_t', 'uint8_t', 'uint16_t', 'uint32_t', 'uint64_t', 'string', 'string_view', 'String']);
const KEYWORDS = new Set(['if', 'else', 'for', 'while', 'do', 'switch', 'case', 'default', 'return', 'break', 'continue', 'throw', 'try', 'catch', 'finally', 'new', 'delete', 'sizeof', 'goto', 'class', 'struct', 'enum', 'typedef', 'using', 'namespace', 'template', 'public', 'private', 'protected', 'static', 'const', 'final', 'virtual', 'inline', 'constexpr', 'operator', 'this', 'true', 'false', 'null', 'nullptr', 'NULL', 'instanceof', 'import', 'package', 'interface', 'extends', 'implements', 'void']);
const QUALS = new Set(['const', 'volatile', 'static', 'final', 'constexpr', 'mutable', 'inline', 'register', 'extern', 'typename', 'struct', 'class', 'enum', 'public', 'private', 'protected', 'virtual', 'explicit', 'friend', 'abstract', 'synchronized', 'transient', 'unsigned_', 'thread_local']);
const BINPREC = {
  '||': 4, '&&': 5, '|': 6, '^': 7, '&': 8, '==': 9, '!=': 9, '<': 10, '<=': 10, '>': 10, '>=': 10, '<=>': 10,
  '<<': 11, '>>': 11, '>>>': 11, '+': 12, '-': 12, '*': 13, '/': 13, '%': 13,
};
const ASSIGN = new Set(['=', '+=', '-=', '*=', '/=', '%=', '&=', '|=', '^=', '<<=', '>>=', '>>>=']);

const SIZE_WORDS = { 'long long': 'long', 'long long int': 'long', 'long int': 'long', 'short int': 'int', 'unsigned int': 'uint', 'unsigned': 'uint', 'unsigned long': 'ulong', 'unsigned long long': 'ulong', 'unsigned short': 'uint', 'unsigned char': 'uchar', 'signed': 'int', 'long double': 'double' };

export function parse(src, lang) {
  let lexed;
  try { lexed = lex(src, lang); } catch (e) { if (e instanceof LexError) throw new ParseError(e.message, e.line); throw e; }
  return new Parser(lexed.toks, lang).program();
}

class Parser {
  constructor(toks, lang) {
    this.toks = toks;
    this.lang = lang;
    this.p = 0;
    this.sub = 0; // consumed '>' characters inside a '>>' / '>>>' token (template closing)
    this.prims = new Set(PRIMS);
    if (lang === 'cpp') this.prims.delete('var'); else this.prims.delete('size_t');
    this.typeNames = new Set();
    this.templateParams = new Set();
    this.prescan();
  }

  // ---- token helpers
  get tok() {
    const t = this.toks[this.p];
    if (this.sub && t.t === 'op' && /^>+$/.test(t.v)) return { ...t, v: t.v.slice(this.sub) };
    return t;
  }
  peekAt(k = 1) { return this.toks[Math.min(this.p + k, this.toks.length - 1)]; }
  is(v) { const t = this.tok; return (t.t === 'op' || t.t === 'id') && t.v === v; }
  isOp(v) { const t = this.tok; return t.t === 'op' && t.v === v; }
  isId(v) { const t = this.tok; return t.t === 'id' && t.v === v; }
  next() { const t = this.tok; this.p++; this.sub = 0; return t; }
  save() { return { p: this.p, sub: this.sub }; }
  restore(s) { this.p = s.p; this.sub = s.sub; }
  accept(v) { if (this.is(v)) { this.next(); return true; } return false; }
  expect(v) {
    if (!this.is(v)) throw new ParseError(`Expected "${v}" but found "${this.tok.v}"`, this.tok.line);
    return this.next();
  }
  ident() {
    const t = this.tok;
    if (t.t !== 'id') throw new ParseError(`Expected a name but found "${t.v}"`, t.line);
    this.next();
    return t.v;
  }
  fail(msg) { throw new ParseError(msg, this.tok.line); }
  closeAngle() {
    const t = this.toks[this.p];
    if (t.t === 'op' && /^>+$/.test(t.v)) {
      const left = t.v.length - this.sub;
      if (left === 1) { this.p++; this.sub = 0; } else this.sub++;
      return true;
    }
    return false;
  }
  atCloseAngle() { const t = this.tok; return t.t === 'op' && /^>+$/.test(t.v); }

  prescan() {
    const t = this.toks;
    for (let i = 0; i < t.length - 1; i++) {
      if (t[i].t === 'id' && ['class', 'struct', 'enum', 'interface'].includes(t[i].v) && t[i + 1].t === 'id' && !(t[i - 1] && t[i - 1].v === '.')) this.typeNames.add(t[i + 1].v);
      if (t[i].t === 'id' && t[i].v === 'typedef') {
        let j = i + 1;
        while (j < t.length && t[j].v !== ';') j++;
        if (t[j - 1].t === 'id') this.typeNames.add(t[j - 1].v);
      }
      if (t[i].t === 'id' && t[i].v === 'using' && t[i + 1].t === 'id' && t[i + 2] && t[i + 2].v === '=') this.typeNames.add(t[i + 1].v);
      if (t[i].t === 'id' && t[i].v === 'template' && t[i + 1].v === '<') {
        let j = i + 2, d = 1;
        while (j < t.length && d) { if (t[j].v === '<') d++; else if (t[j].v === '>') d--; else if (t[j].v === '>>') d -= 2; if (t[j].t === 'id' && !['typename', 'class', 'int', 'size_t'].includes(t[j].v) && t[j - 1] && ['typename', 'class'].includes(t[j - 1].v)) this.typeNames.add(t[j].v); j++; }
      }
      // Java generic method <T> / class Foo<T>
      if (this.lang === 'java' && t[i].v === '<' && t[i + 1].t === 'id' && (t[i + 2].v === '>' || t[i + 2].v === ',' || t[i + 2].v === 'extends') && /^[A-Z]$/.test(t[i + 1].v)) this.typeNames.add(t[i + 1].v);
    }
  }

  // ---- program
  program() {
    const items = [];
    while (this.tok.t !== 'eof') {
      const it = this.topLevel();
      if (it) items.push(...(Array.isArray(it) ? it : [it]));
    }
    return { k: 'program', items, lang: this.lang };
  }

  skipTemplateHeader() {
    if (this.isId('template') && this.peekAt().v === '<') {
      this.next(); this.next();
      let d = 1;
      while (d && this.tok.t !== 'eof') { const v = this.next().v; if (v === '<') d++; else if (v === '>') d--; else if (v === '>>') d -= 2; }
      return true;
    }
    return false;
  }

  topLevel() {
    const t = this.tok;
    if (this.accept(';')) return null;
    if (this.isId('import') || this.isId('package')) { while (!this.isOp(';') && this.tok.t !== 'eof') this.next(); this.accept(';'); return null; }
    if (this.isId('using')) {
      this.next();
      if (this.isId('namespace')) { while (!this.isOp(';')) this.next(); this.next(); return null; }
      const name = this.ident();
      if (this.accept('=')) { const ty = this.parseType(); this.accept(';'); this.typeNames.add(name); return { k: 'typedef', name, type: ty, line: t.line }; }
      while (!this.isOp(';')) this.next();
      this.next();
      return null;
    }
    if (this.isId('typedef')) {
      this.next();
      const ty = this.parseType();
      const name = this.ident();
      this.accept(';');
      this.typeNames.add(name);
      return { k: 'typedef', name, type: ty, line: t.line };
    }
    if (this.isId('namespace')) { this.next(); if (this.tok.t === 'id') this.next(); this.expect('{'); const items = []; while (!this.isOp('}')) { const it = this.topLevel(); if (it) items.push(...(Array.isArray(it) ? it : [it])); } this.next(); return items; }
    if (this.isOp('@')) { this.skipAnnotation(); return null; }
    this.skipTemplateHeader();
    return this.member(null);
  }

  skipAnnotation() {
    this.expect('@');
    this.ident();
    while (this.accept('.')) this.ident();
    if (this.isOp('(')) { let d = 0; do { if (this.isOp('(')) d++; if (this.isOp(')')) d--; this.next(); } while (d); }
  }

  // class / struct / interface / enum, or a function / field declaration. `cls` is the enclosing class node.
  member(cls) {
    const startLine = this.tok.line;
    const mods = { static: false, isFinal: false, access: cls && cls.kind === 'class' && this.lang === 'cpp' ? 'private' : 'public' };
    for (;;) {
      if (this.isOp('@')) { this.skipAnnotation(); continue; }
      const t = this.tok;
      if (t.t === 'id' && ['public', 'private', 'protected'].includes(t.v)) {
        if (this.peekAt().v === ':') { this.next(); this.next(); this.cppAccess = t.v; continue; }
        mods.access = t.v; this.next(); continue;
      }
      if (t.t === 'id' && ['static', 'final', 'abstract', 'synchronized', 'native', 'transient', 'volatile', 'inline', 'virtual', 'explicit', 'friend', 'constexpr', 'mutable', 'extern', 'default', 'strictfp'].includes(t.v) && !(t.v === 'default' && this.peekAt().v === ':')) {
        if (t.v === 'static') mods.static = true;
        if (t.v === 'final') mods.isFinal = true;
        this.next();
        continue;
      }
      break;
    }
    if (this.isId('template')) this.skipTemplateHeader();
    if (this.isId('class') || this.isId('struct') || this.isId('interface') || (this.isId('enum') )) {
      const kind = this.next().v;
      if (this.isId('class') && kind === 'enum') this.next();
      if (this.tok.t !== 'id') { // anonymous struct { } x;
        this.fail('Anonymous struct/class declarations are not supported');
      }
      const name = this.ident();
      this.typeNames.add(name);
      let base = null;
      if (this.isOp('<')) { this.skipAngles(); }
      if (kind !== 'enum') {
        while (this.isId('extends') || this.isId('implements') || this.isOp(':')) {
          this.next();
          do { while (QUALS.has(this.tok.v)) this.next(); const b = this.parseType(); if (!base) base = b; } while (this.accept(','));
        }
      } else if (this.isOp(':')) { this.next(); this.parseType(); }
      if (this.isOp(';')) { this.next(); return null; } // forward declaration
      const node = { k: 'class', kind, name, base, line: startLine, fields: [], methods: [], ctors: [], inner: [], enumValues: null, static: mods.static };
      this.expect('{');
      this.classBody(node);
      node.endLine = this.tok.line;
      this.expect('}');
      // `struct X {...} var;`
      if (this.lang === 'cpp' && this.tok.t === 'id' && !KEYWORDS.has(this.tok.v) && !this.typeNames.has(this.tok.v) && !this.prims.has(this.tok.v)) { while (!this.isOp(';') && this.tok.t !== 'eof') this.next(); }
      this.accept(';');
      return node;
    }
    return this.funcOrField(cls, mods, startLine);
  }

  classBody(node) {
    const saved = this.cppAccess;
    this.cppAccess = node.kind === 'struct' || node.kind === 'interface' ? 'public' : (this.lang === 'java' ? 'public' : 'private');
    if (node.kind === 'enum') {
      node.enumValues = [];
      let ord = 0;
      while (!this.isOp('}') && !this.isOp(';')) {
        if (this.isOp('@')) this.skipAnnotation();
        const nm = this.ident();
        let val = null;
        if (this.accept('=')) val = this.parseAssign();
        if (this.isOp('(')) { this.next(); while (!this.isOp(')')) this.next(); this.next(); }
        node.enumValues.push({ name: nm, value: val, ord: ord++ });
        if (!this.accept(',')) break;
      }
      if (this.accept(';')) {
        while (!this.isOp('}') && this.tok.t !== 'eof') { const m = this.member(node); this.addMember(node, m); }
      }
      this.cppAccess = saved;
      return;
    }
    while (!this.isOp('}')) {
      if (this.tok.t === 'eof') this.fail('Unexpected end of file inside a class');
      if (this.accept(';')) continue;
      const m = this.member(node);
      this.addMember(node, m);
    }
    this.cppAccess = saved;
  }

  addMember(node, m) {
    for (const x of Array.isArray(m) ? m : [m]) {
      if (!x) continue;
      if (x.k === 'func') { if (x.isCtor) node.ctors.push(x); else node.methods.push(x); } else if (x.k === 'field') node.fields.push(x);
      else if (x.k === 'class') node.inner.push(x);
      else if (x.k === 'init') node.fields.push(x);
    }
  }

  skipAngles() {
    this.expect('<');
    let d = 1;
    while (d && this.tok.t !== 'eof') { const v = this.next().v; if (v === '<') d++; else if (v === '>') d--; else if (v === '>>') d -= 2; }
  }

  funcOrField(cls, mods, startLine) {
    // static / instance initializer block (Java)
    if (this.isOp('{')) { const body = this.block(); return { k: 'init', static: mods.static, body, line: startLine }; }
    // Java generic method header: <T> ...
    if (this.lang === 'java' && this.isOp('<')) this.skipAngles();
    const save = this.save();
    // constructor / destructor: Name( or ~Name(
    if (cls && (this.tok.v === cls.name || this.isOp('~')) && (this.peekAt().v === '(' || this.isOp('~'))) {
      const isDtor = this.accept('~');
      const nameTok = this.next();
      void nameTok;
      const params = this.parseParams();
      while (this.isId('const') || this.isId('noexcept') || this.isId('throws')) { this.next(); if (this.tok.t === 'id' && this.peekAt().v !== '{') this.next(); }
      let initList = [];
      if (this.isOp(':')) {
        this.next();
        do {
          const nm = this.ident();
          let args;
          if (this.isOp('(')) args = this.parseArgs(); else { this.expect('{'); args = []; while (!this.isOp('}')) { args.push(this.parseAssign()); if (!this.accept(',')) break; } this.expect('}'); }
          initList.push({ name: nm, args });
        } while (this.accept(','));
      }
      if (this.accept('=')) { this.next(); this.accept(';'); return null; }
      if (this.isOp(';')) { this.next(); return null; }
      const body = this.block();
      if (isDtor) return null;
      return { k: 'func', name: cls.name, params, ret: null, body, line: startLine, endLine: body.endLine, isStatic: false, isCtor: true, initList, cls: cls.name, access: mods.access };
    }
    // operator conversion etc. are unsupported; try  <type> <name> ...
    let ret;
    try { ret = this.parseType(); } catch (e) { this.restore(save); throw e; }
    let name;
    if (this.isId('operator')) {
      this.next();
      let op = this.next().v;
      if (op === '(' ) { this.expect(')'); op = '()'; } else if (op === '[') { this.expect(']'); op = '[]'; }
      name = `operator${op}`;
    } else {
      if (this.tok.t !== 'id') this.fail(`Unexpected "${this.tok.v}" in declaration`);
      name = this.next().v;
      while (this.isOp('::')) { this.next(); name = this.ident(); } // out-of-class definition: Solution::foo
    }
    if (ret.isStatic) mods.static = true;
    if (this.isOp('(')) {
      const params = this.parseParams();
      while (this.isId('const') || this.isId('noexcept') || this.isId('override') || this.isId('final')) this.next();
      if (this.isId('throws')) { this.next(); do { this.parseType(); } while (this.accept(',')); }
      if (this.accept('=')) { this.next(); this.accept(';'); return null; } // = default / = delete / = 0
      if (this.isOp(';')) { this.next(); return null; } // prototype
      const body = this.block();
      return { k: 'func', name, params, ret, body, line: startLine, endLine: body.endLine, isStatic: mods.static, isCtor: false, cls: cls ? cls.name : null, access: mods.access };
    }
    // field(s) / global variable(s)
    const decls = [];
    for (;;) {
      let ty = ret;
      let dims = 0;
      while (this.isOp('*') || this.isOp('&')) { ty = { ...ty, ptr: ty.ptr + (this.next().v === '*' ? 1 : 0) }; if (this.isOp('*')) continue; }
      let nm = name;
      if (decls.length) nm = this.ident();
      while (this.isOp('[')) { this.next(); let size = null; if (!this.isOp(']')) size = this.parseAssign(); this.expect(']'); ty = { ...ty, arr: [...(ty.arr || []), size] }; dims++; }
      let init = null;
      if (this.accept('=')) init = this.initializer();
      else if (this.isOp('{') ) init = this.initializer();
      else if (this.isOp('(') ) { init = { k: 'ctorcall', args: this.parseArgs(), line: this.tok.line }; }
      decls.push({ k: 'field', name: nm, type: ty, init, static: mods.static, line: startLine, access: mods.access, isConst: ret.isConst });
      if (!this.accept(',')) break;
    }
    this.expect(';');
    return decls;
  }

  parseParams() {
    this.expect('(');
    const params = [];
    if (this.isId('void') && this.peekAt().v === ')') { this.next(); this.next(); return params; }
    while (!this.isOp(')')) {
      if (this.isOp('@')) this.skipAnnotation();
      while (this.isId('final')) this.next();
      if (this.isOp('...')) { this.next(); continue; }
      let ty = this.parseType();
      let name = '';
      if (this.isOp('...')) { this.next(); ty = { ...ty, dims: (ty.dims || 0) + 1, varargs: true }; }
      if (this.tok.t === 'id') name = this.next().v;
      while (this.isOp('[')) { this.next(); if (!this.isOp(']')) this.parseAssign(); this.expect(']'); ty = { ...ty, dims: (ty.dims || 0) + 1 }; }
      let def = null;
      if (this.accept('=')) def = this.parseAssign();
      params.push({ type: ty, name, def });
      if (!this.accept(',')) break;
    }
    this.expect(')');
    return params;
  }

  // ---- types
  isTypeStart() {
    const t = this.tok;
    if (t.t !== 'id') return false;
    if (this.prims.has(t.v) || QUALS.has(t.v)) return true;
    if (this.typeNames.has(t.v)) return true;
    return false;
  }

  /** Parse a type. Throws ParseError if the tokens cannot be a type. */
  parseType() {
    let isConst = false, isStatic = false;
    while (this.tok.t === 'id' && QUALS.has(this.tok.v) && !(this.tok.v === 'class' || this.tok.v === 'struct' || this.tok.v === 'enum') ) { if (this.tok.v === 'const' || this.tok.v === 'final') isConst = true; if (this.tok.v === 'static') isStatic = true; this.next(); }
    if (this.tok.t === 'id' && ['class', 'struct', 'enum'].includes(this.tok.v) && this.peekAt().t === 'id' && this.peekAt(2).v !== '{' && this.peekAt(2).v !== ':') this.next(); // elaborated type specifier
    const t = this.tok;
    if (t.t !== 'id') throw new ParseError(`Expected a type but found "${t.v}"`, t.line);
    if (KEYWORDS.has(t.v) && !this.prims.has(t.v) && !QUALS.has(t.v)) throw new ParseError(`Expected a type but found "${t.v}"`, t.line);
    // builtin multi-word types
    let name;
    const words = [];
    if (['unsigned', 'signed', 'long', 'short'].includes(t.v)) {
      while (this.tok.t === 'id' && ['unsigned', 'signed', 'long', 'short', 'int', 'char', 'double'].includes(this.tok.v)) words.push(this.next().v);
      const joined = words.join(' ');
      name = SIZE_WORDS[joined] || (words.includes('char') ? (words[0] === 'unsigned' ? 'uchar' : 'char') : words.includes('double') ? 'double' : words.includes('long') ? 'long' : 'int');
      if (words[0] === 'unsigned' && words.length === 1) name = 'uint';
      if (words[0] === 'unsigned' && words.includes('long')) name = 'ulong';
      if (words[0] === 'unsigned' && words.includes('int') && !words.includes('long')) name = 'uint';
    } else {
      name = this.next().v;
      while (this.lang === 'java' && this.isOp('.') && this.peekAt().t === 'id' && /^[A-Za-z]/.test(this.peekAt().v) && (/^[A-Z]/.test(name) || /^[a-z]+$/.test(name)) && this.dottedTypeOk()) { this.next(); name = this.next().v; }
      if (name === 'decltype' && this.isOp('(')) { let d = 0; do { if (this.isOp('(')) d++; if (this.isOp(')')) d--; this.next(); } while (d); name = 'auto'; }
      while (this.isOp('::') && this.peekAt().t === 'id') { this.next(); name = this.next().v; }
      if (name === 'std' && this.isOp('::')) { this.next(); name = this.ident(); }
    }
    const NORMAL = { boolean: 'bool', byte: 'int', int8_t: 'int', int16_t: 'int', int32_t: 'int', int64_t: 'long', uint8_t: 'uchar', uint16_t: 'uint', uint32_t: 'uint', uint64_t: 'ulong', size_t: 'ulong', wchar_t: 'char', Integer: 'Integer', Long: 'Long', Double: 'Double', Character: 'Character', Boolean: 'Boolean', string: 'string', string_view: 'string', String: 'string', float: 'double', Float: 'double', ssize_t: 'long' };
    name = NORMAL[name] || name;
    const ty = { k: 'type', name, args: [], ptr: 0, ref: false, dims: 0, isConst, line: t.line };
    if (isStatic) ty.isStatic = true;
    // template arguments
    if (this.isOp('<') && (this.typeNames.has(name) || /^[a-z_]+$/.test(name) || /^[A-Z]/.test(name)) && !this.prims.has(name)) {
      const save = this.save();
      try {
        this.next();
        if (!this.atCloseAngle()) {
          for (;;) {
            if (this.isOp('?')) { this.next(); if (this.isId('extends') || this.isId('super')) { this.next(); ty.args.push(this.parseType()); } else ty.args.push({ k: 'type', name: 'Object', args: [], ptr: 0, ref: false, dims: 0 }); }
            else if (this.tok.t === 'num') ty.args.push({ k: 'num', value: this.next().v });
            else ty.args.push(this.parseType());
            if (this.isId('extends') || this.isId('super')) { this.next(); this.parseType(); }
            if (!this.accept(',')) break;
          }
        }
        if (!this.closeAngle()) throw new ParseError('Expected ">"', this.tok.line);
      } catch (e) {
        this.restore(save);
        if (!(e instanceof ParseError)) throw e;
        // not a template after all (e.g. `a < b`); leave `<` for the expression parser
        ty.args = [];
        ty.notTemplate = true;
      }
    }
    // dependent names: vector<int>::iterator, map<..>::const_iterator
    while (this.isOp('::') && this.peekAt().t === 'id' && !ty.notTemplate && ty.args.length) { this.next(); ty.nested = this.ident(); ty.name = `${ty.name}::${ty.nested}`; }
    for (;;) {
      if (this.isOp('*')) { this.next(); ty.ptr++; while (this.isId('const')) this.next(); continue; }
      if (this.isOp('&')) { this.next(); ty.ref = true; continue; }
      if (this.isOp('&&')) { this.next(); ty.ref = true; continue; }
      if (this.isId('const')) { this.next(); ty.isConst = true; continue; }
      if (this.tok.t === 'id' && ['static', 'inline', 'constexpr'].includes(this.tok.v) && this.peekAt().t === 'id') { if (this.tok.v === 'static') ty.isStatic = true; this.next(); continue; }
      if (this.isOp('[') && this.peekAt().v === ']') { this.next(); this.next(); ty.dims++; continue; }
      break;
    }
    return ty;
  }

  // Java: `Map.Entry<K,V> e` / `java.util.List<T> x` -- only a type when a name follows the (generic) type
  dottedTypeOk() {
    let k = 1, depth = 0;
    for (;;) {
      const t = this.peekAt(k);
      if (t.t === 'eof') return false;
      if (t.v === '<') depth++;
      else if (t.v === '>') depth--;
      else if (t.v === '>>') depth -= 2;
      else if (depth <= 0 && t.t === 'id' && !KEYWORDS.has(t.v) && k > 1 && this.peekAt(k - 1).v !== '.') return true;
      else if (depth <= 0 && t.t === 'op' && !['.', '>', '>>', '[', ']'].includes(t.v)) return false;
      else if (depth <= 0 && t.t === 'id' && this.peekAt(k - 1).v === '.') { /* continue dotted chain */ }
      k++;
      if (k > 40) return false;
    }
  }

  /** Speculatively check whether a declaration starts here: `Type name [= ; , ( [ : {]`. */
  looksLikeDecl() {
    const t = this.tok;
    if (t.t !== 'id') return false;
    if (KEYWORDS.has(t.v) && !this.prims.has(t.v) && !QUALS.has(t.v)) return false;
    const save = this.save();
    try {
      if ((t.v === 'auto' || (t.v === 'var' && this.lang === 'java'))) { this.restore(save); return true; }
      const ty = this.parseType();
      void ty;
      if (this.isOp('[') && this.peekAt().t === 'id') { /* auto [a, b] */ }
      if (this.tok.t === 'id' && !KEYWORDS.has(this.tok.v)) {
        const after = this.peekAt();
        const ok = after.t === 'op' && ['=', ';', ',', '(', '[', ':', '{', ')'].includes(after.v);
        this.restore(save);
        return ok;
      }
      // `auto& [a,b] = ...` / `auto [a,b]`
      if (this.isOp('[') && ty.name === 'auto' && this.peekAt().t === 'id') { this.restore(save); return true; }
      this.restore(save);
      return false;
    } catch (e) {
      this.restore(save);
      if (e instanceof ParseError) return false;
      throw e;
    }
  }

  // ---- statements
  block() {
    const line = this.tok.line;
    this.expect('{');
    const stmts = [];
    while (!this.isOp('}')) {
      if (this.tok.t === 'eof') this.fail('Missing "}" before the end of the file');
      stmts.push(this.statement());
    }
    const endLine = this.tok.line;
    this.next();
    return { k: 'block', stmts, line, endLine };
  }

  statement() {
    const t = this.tok;
    const line = t.line;
    if (t.t === 'op') {
      if (t.v === '{') return this.block();
      if (t.v === ';') { this.next(); return { k: 'empty', line }; }
      if (t.v === '@') { this.skipAnnotation(); return this.statement(); }
    }
    if (t.t === 'id') {
      switch (t.v) {
        case 'if': {
          this.next(); this.expect('(');
          const cond = this.parseExprNoComma(true);
          this.expect(')');
          const then = this.statement();
          let els = null;
          if (this.isId('else')) { this.next(); els = this.statement(); }
          return { k: 'if', cond, then, else: els, line };
        }
        case 'while': {
          this.next(); this.expect('(');
          const cond = this.parseExpr();
          this.expect(')');
          return { k: 'while', cond, body: this.statement(), line };
        }
        case 'do': {
          this.next();
          const body = this.statement();
          this.expect('while'); this.expect('(');
          const cond = this.parseExpr();
          this.expect(')'); this.accept(';');
          return { k: 'dowhile', cond, body, line };
        }
        case 'for': return this.forStatement();
        case 'return': {
          this.next();
          let e = null;
          if (!this.isOp(';')) e = this.initializer();
          this.expect(';');
          return { k: 'return', expr: e, line };
        }
        case 'break': this.next(); this.accept(this.tok.t === 'id' && this.tok.v !== ';' ? this.tok.v : ';'); this.accept(';'); return { k: 'break', line };
        case 'continue': this.next(); if (this.tok.t === 'id') this.next(); this.accept(';'); return { k: 'continue', line };
        case 'throw': { this.next(); const e = this.isOp(';') ? null : this.parseExpr(); this.accept(';'); return { k: 'throw', expr: e, line }; }
        case 'try': return this.tryStatement();
        case 'switch': return this.switchStatement();
        case 'delete': { this.next(); if (this.isOp('[')) { this.next(); this.expect(']'); } const e = this.parseExpr(); this.accept(';'); return { k: 'expr', expr: { k: 'delete', expr: e, line }, line }; }
        case 'typedef': case 'using': { const it = this.topLevel(); return { k: 'typedefStmt', item: it, line }; }
        case 'class': case 'struct': case 'enum': {
          if (this.peekAt().t === 'id' && (this.peekAt(2).v === '{' || this.peekAt(2).v === ':' )) { const c = this.member(null); return { k: 'localClass', cls: c, line }; }
          break;
        }
        case 'static_assert': { while (!this.isOp(';')) this.next(); this.next(); return { k: 'empty', line }; }
        default: break;
      }
      // labeled statement (rare) -> skip label
      if (this.peekAt().v === ':' && this.peekAt(2).v !== ':' && !KEYWORDS.has(t.v) && !this.isTypeStart() && this.peekAt().t === 'op') { this.next(); this.next(); return this.statement(); }
      if (this.looksLikeDecl()) return this.declStatement();
    }
    const e = this.parseExpr();
    this.expect(';');
    return { k: 'expr', expr: e, line };
  }

  declStatement(noSemi = false) {
    const line = this.tok.line;
    let baseType = this.parseType();
    // structured binding: auto [a, b] = expr;
    if (this.isOp('[') && baseType.name === 'auto') {
      this.next();
      const names = [];
      while (!this.isOp(']')) { names.push(this.ident()); if (!this.accept(',')) break; }
      this.expect(']');
      this.expect('=');
      const init = this.parseAssign();
      if (!noSemi) this.expect(';');
      return { k: 'bind', names, init, type: baseType, line };
    }
    const decls = [];
    for (;;) {
      let ty = baseType;
      while (this.isOp('*') || this.isOp('&')) { const o = this.next().v; ty = { ...ty, ptr: ty.ptr + (o === '*' ? 1 : 0), ref: o === '&' ? true : ty.ref }; }
      const nameTok = this.tok;
      const name = this.ident();
      while (this.isOp('[')) { this.next(); let size = null; if (!this.isOp(']')) size = this.parseAssign(); this.expect(']'); if (this.lang === 'java') ty = { ...ty, dims: ty.dims + 1 }; else ty = { ...ty, arr: [...(ty.arr || []), size] }; }
      let init = null;
      if (this.accept('=')) init = this.initializer();
      else if (this.isOp('(')) init = { k: 'ctorcall', args: this.parseArgs(), line: nameTok.line };
      else if (this.isOp('{')) { const il = this.initializer(); init = { k: 'ctorcall', args: il.items, brace: true, line: nameTok.line }; }
      decls.push({ name, type: ty, init, line: nameTok.line });
      if (!this.accept(',')) break;
    }
    if (!noSemi) this.expect(';');
    return { k: 'decl', decls, line };
  }

  initializer() {
    if (this.isOp('{')) return this.initList();
    return this.parseAssign();
  }

  initList() {
    const line = this.tok.line;
    this.expect('{');
    const items = [];
    while (!this.isOp('}')) {
      items.push(this.isOp('{') ? this.initList() : this.parseAssign());
      if (!this.accept(',')) break;
    }
    this.expect('}');
    return { k: 'initlist', items, line };
  }

  forStatement() {
    const line = this.tok.line;
    this.next();
    this.expect('(');
    // range-for: for (T x : expr) / for (auto& [k, v] : m)
    const save = this.save();
    if (this.looksLikeDecl() || this.isId('auto')) {
      let head = null;
      try {
        const ty = this.parseType();
        let names = null, name = null;
        if (this.isOp('[')) { this.next(); names = []; while (!this.isOp(']')) { names.push(this.ident()); if (!this.accept(',')) break; } this.expect(']'); } else name = this.ident();
        if (this.isOp(':')) head = { ty, names, name };
      } catch (e) { if (!(e instanceof ParseError)) throw e; }
      if (head) {
        this.next();
        const coll = this.parseExpr();
        this.expect(')');
        return { k: 'foreach', type: head.ty, name: head.name, names: head.names, coll, body: this.statement(), line };
      }
      this.restore(save);
    }
    let init = null;
    if (!this.isOp(';')) {
      if (this.looksLikeDecl()) init = this.declStatement(true);
      else init = { k: 'expr', expr: this.parseExpr(), line };
    }
    this.expect(';');
    const cond = this.isOp(';') ? null : this.parseExpr();
    this.expect(';');
    const update = this.isOp(')') ? null : this.parseExpr();
    this.expect(')');
    return { k: 'for', init, cond, update, body: this.statement(), line };
  }

  switchStatement() {
    const line = this.tok.line;
    this.next(); this.expect('(');
    const disc = this.parseExpr();
    this.expect(')'); this.expect('{');
    const cases = [];
    let cur = null;
    while (!this.isOp('}')) {
      if (this.isId('case') || this.isId('default')) {
        const isDefault = this.next().v === 'default';
        let test = null;
        const tests = [];
        if (!isDefault) {
          test = this.parseTernary();
          tests.push(test);
          while (this.isOp(',')) { this.next(); tests.push(this.parseTernary()); }
        }
        let arrow = false;
        if (this.isOp('->')) { this.next(); arrow = true; } else this.expect(':');
        cur = { tests, isDefault, body: [], arrow, line: this.tok.line };
        cases.push(cur);
        if (arrow) { cur.body.push(this.statement()); cur = null; }
        continue;
      }
      if (!cur) this.fail('Statement before the first "case" in a switch');
      cur.body.push(this.statement());
    }
    this.next();
    return { k: 'switch', disc, cases, line };
  }

  tryStatement() {
    const line = this.tok.line;
    this.next();
    if (this.isOp('(')) { // try-with-resources: skip resource list
      let d = 0; do { if (this.isOp('(')) d++; if (this.isOp(')')) d--; this.next(); } while (d);
    }
    const body = this.block();
    const catches = [];
    let fin = null;
    while (this.isId('catch')) {
      this.next(); this.expect('(');
      const types = [];
      this.accept('final');
      do { if (this.isOp('...')) { this.next(); types.push({ k: 'type', name: '...', args: [], ptr: 0, ref: false, dims: 0 }); } else types.push(this.parseType()); } while (this.accept('|'));
      let name = null;
      if (this.tok.t === 'id') name = this.next().v;
      this.expect(')');
      catches.push({ types, name, body: this.block() });
    }
    if (this.isId('finally')) { this.next(); fin = this.block(); }
    return { k: 'try', body, catches, fin, line };
  }

  // ---- expressions
  parseExpr() {
    let e = this.parseAssign();
    while (this.isOp(',')) { const line = this.tok.line; this.next(); const r = this.parseAssign(); e = { k: 'comma', left: e, right: r, line }; }
    return e;
  }
  parseExprNoComma() { return this.parseAssign(); }

  parseAssign() {
    const left = this.parseTernary();
    const t = this.tok;
    if (t.t === 'op' && ASSIGN.has(t.v)) {
      this.next();
      const right = this.isOp('{') ? this.initList() : this.parseAssign();
      return { k: 'assign', op: t.v, target: left, value: right, line: t.line };
    }
    return left;
  }

  parseTernary() {
    const cond = this.parseBinary(4);
    if (this.isOp('?')) {
      const line = this.tok.line;
      this.next();
      const a = this.parseAssign();
      this.expect(':');
      const b = this.parseAssign();
      return { k: 'cond', cond, a, b, line };
    }
    return cond;
  }

  parseBinary(minPrec) {
    let left = this.parseUnary();
    for (;;) {
      const t = this.tok;
      if (t.t === 'id' && t.v === 'instanceof' && minPrec <= 10) {
        this.next();
        const ty = this.parseType();
        let bind = null;
        if (this.tok.t === 'id' && !KEYWORDS.has(this.tok.v)) bind = this.next().v;
        left = { k: 'instanceof', expr: left, type: ty, bind, line: t.line };
        continue;
      }
      if (t.t !== 'op') break;
      const prec = BINPREC[t.v];
      if (prec === undefined || prec < minPrec) break;
      // a '>' that closes a template argument list is handled by parseType; here it is a comparison
      this.next();
      const right = this.parseBinary(prec + 1);
      left = { k: 'bin', op: t.v, left, right, line: t.line };
    }
    return left;
  }

  isCastAhead() {
    // at '(' : (primitive-type [*&]) followed by an operand  or (UserType) followed by an obvious operand
    const save = this.save();
    try {
      this.next();
      const first = this.tok;
      if (first.t !== 'id') { this.restore(save); return false; }
      const prim = this.prims.has(first.v) && !(first.v === 'auto' || first.v === 'var') || ['unsigned', 'signed', 'long', 'short'].includes(first.v);
      if (!prim && !this.typeNames.has(first.v) && !/^(Integer|Long|Double|Character|Boolean|Object|Comparable)$/.test(first.v) && !(first.v === 'std')) { this.restore(save); return false; }
      const ty = this.parseType();
      if (!this.isOp(')')) { this.restore(save); return false; }
      this.next();
      const n = this.tok;
      let ok;
      if (prim || ty.ptr) ok = !(n.t === 'op' && [')', ']', ';', ',', '=', '==', '!=', '<', '>', '<=', '>=', '?', ':', '*', '/', '%', '&&', '||', '|', '^', '<<', '>>', '.', '->'].includes(n.v) && !(n.v === '*' && ty.ptr === 0 && false));
      else ok = n.t === 'id' || n.t === 'num' || n.t === 'str' || n.t === 'chr' || (n.t === 'op' && ['(', '!', '~'].includes(n.v));
      if (prim && n.t === 'op' && ['-', '+', '&', '*'].includes(n.v)) ok = true;
      this.restore(save);
      return ok;
    } catch (e) {
      this.restore(save);
      if (e instanceof ParseError) return false;
      throw e;
    }
  }

  isLambdaAhead() {
    // Java:  x -> ...   (a, b) -> ...   (int a, int b) -> ...   () -> ...
    if (this.lang !== 'java') return false;
    if (this.tok.t === 'id' && this.peekAt().v === '->') return true;
    if (!this.isOp('(')) return false;
    let d = 0, k = 0;
    for (;;) {
      const t = this.peekAt(k);
      if (t.t === 'eof') return false;
      if (t.v === '(') d++;
      if (t.v === ')') { d--; if (d === 0) return this.peekAt(k + 1).v === '->'; }
      k++;
    }
  }

  parseUnary() {
    const t = this.tok;
    const line = t.line;
    if (t.t === 'op') {
      switch (t.v) {
        case '!': case '~': case '-': case '+': { this.next(); return { k: 'unary', op: t.v, expr: this.parseUnary(), line }; }
        case '++': case '--': { this.next(); return { k: 'preinc', op: t.v, expr: this.parseUnary(), line }; }
        case '*': { this.next(); return { k: 'deref', expr: this.parseUnary(), line }; }
        case '&': { this.next(); return { k: 'addr', expr: this.parseUnary(), line }; }
        case '(': {
          if (this.isLambdaAhead()) return this.javaLambda();
          if (this.isCastAhead()) {
            this.next();
            const ty = this.parseType();
            this.expect(')');
            return { k: 'cast', type: ty, expr: this.parseUnary(), line };
          }
          break;
        }
        default: break;
      }
    }
    if (t.t === 'id') {
      if (t.v === 'sizeof') {
        this.next();
        if (this.isOp('(')) {
          const save = this.save();
          this.next();
          try { const ty = this.parseType(); if (this.isOp(')') || this.isOp('[')) { while (!this.isOp(')')) this.next(); this.next(); return { k: 'sizeof', type: ty, line }; } } catch (e) { if (!(e instanceof ParseError)) throw e; }
          this.restore(save);
        }
        return { k: 'sizeof', expr: this.parseUnary(), line };
      }
      if (t.v === 'new') return this.parseNew();
      if (t.v === 'delete') { this.next(); if (this.isOp('[')) { this.next(); this.expect(']'); } return { k: 'delete', expr: this.parseUnary(), line }; }
      if (t.v === 'throw') { this.next(); return { k: 'throwExpr', expr: this.isOp(';') || this.isOp(')') || this.isOp(':') ? null : this.parseAssign(), line }; }
    }
    return this.parsePostfix();
  }

  javaLambda() {
    const line = this.tok.line;
    const params = [];
    if (this.tok.t === 'id') params.push({ name: this.next().v, type: null });
    else {
      this.expect('(');
      while (!this.isOp(')')) {
        this.accept('final');
        if (this.tok.t === 'id' && (this.peekAt().v === ',' || this.peekAt().v === ')')) params.push({ name: this.next().v, type: null });
        else { const ty = this.parseType(); params.push({ name: this.ident(), type: ty }); }
        if (!this.accept(',')) break;
      }
      this.expect(')');
    }
    this.expect('->');
    let body;
    if (this.isOp('{')) body = this.block();
    else { const e = this.parseAssign(); body = { k: 'block', stmts: [{ k: 'return', expr: e, line: e.line || line }], line, endLine: line, exprBody: true }; }
    return { k: 'lambda', params, body, captures: '&', ret: null, line };
  }

  cppLambda() {
    const line = this.tok.line;
    this.expect('[');
    let cap = '';
    while (!this.isOp(']')) cap += this.next().v;
    this.expect(']');
    let params = [];
    if (this.isOp('(')) params = this.parseParams();
    while (this.isId('mutable') || this.isId('noexcept') || this.isId('constexpr')) this.next();
    let ret = null;
    if (this.isOp('->')) { this.next(); ret = this.parseType(); }
    const body = this.block();
    return { k: 'lambda', params, body, captures: cap, ret, line };
  }

  parseNew() {
    const line = this.tok.line;
    this.next();
    if (this.isOp('(')) { this.next(); while (!this.isOp(')')) this.next(); this.next(); } // placement new
    let ty = this.parseNewType();
    // array: new T[n], new T[n][m], new T[]{...}
    if (this.isOp('[')) {
      const dims = [];
      let extra = 0;
      while (this.isOp('[')) {
        this.next();
        if (this.isOp(']')) { this.next(); extra++; continue; }
        dims.push(this.parseExpr());
        this.expect(']');
      }
      let init = null;
      if (this.isOp('{')) init = this.initList();
      else if (this.isOp('(') && this.peekAt().v === ')') { this.next(); this.next(); }
      return { k: 'newarr', type: ty, dims, extra, init, line };
    }
    if (ty.dims && this.isOp('{')) return { k: 'newarr', type: { ...ty, dims: 0 }, dims: [], extra: ty.dims, init: this.initList(), line };
    let args = [];
    if (this.isOp('(')) args = this.parseArgs();
    else if (this.isOp('{')) args = this.initList().items;
    let body = null;
    if (this.isOp('{') && this.lang === 'java') { // anonymous class
      body = { k: 'class', kind: 'class', name: `${ty.name}$anon${line}`, base: ty, line, fields: [], methods: [], ctors: [], inner: [] };
      this.next();
      this.classBody(body);
      body.endLine = this.tok.line;
      this.expect('}');
      this.typeNames.add(body.name);
    }
    return { k: 'new', type: ty, args, anon: body, line };
  }

  parseNewType() {
    // like parseType but does not swallow '[' (array dims belong to `new`) or '*'
    const save = this.save();
    const t = this.tok;
    const ty = this.parseTypeNoSuffix();
    void save; void t;
    return ty;
  }

  parseTypeNoSuffix() {
    const name = this.tok;
    const ty = this.parseTypeCore();
    void name;
    return ty;
  }

  parseTypeCore() {
    // reuse parseType but stop before '[' : temporarily mask the check
    const saved = this.noArraySuffix;
    this.noArraySuffix = true;
    const origPeek = this.peekAt.bind(this);
    void origPeek;
    try {
      return this.parseTypeStopAtBracket();
    } finally { this.noArraySuffix = saved; }
  }

  parseTypeStopAtBracket() {
    // parse qualifiers / name / template args only
    while (this.tok.t === 'id' && QUALS.has(this.tok.v)) this.next();
    const t = this.tok;
    if (t.t !== 'id') throw new ParseError(`Expected a type after "new" but found "${t.v}"`, t.line);
    let name;
    if (['unsigned', 'signed', 'long', 'short'].includes(t.v)) {
      const words = [];
      while (this.tok.t === 'id' && ['unsigned', 'signed', 'long', 'short', 'int', 'char', 'double'].includes(this.tok.v)) words.push(this.next().v);
      const joined = words.join(' ');
      name = SIZE_WORDS[joined] || (words.includes('char') ? 'char' : words.includes('double') ? 'double' : words.includes('long') ? 'long' : 'int');
    } else {
      name = this.next().v;
      while (this.isOp('::') && this.peekAt().t === 'id') { this.next(); name = this.next().v; }
      while (this.isOp('.') && this.lang === 'java' && this.peekAt().t === 'id') { this.next(); name = this.next().v; }
    }
    const NORMAL = { boolean: 'bool', byte: 'int', Integer: 'Integer', Long: 'Long', String: 'string', size_t: 'ulong', int64_t: 'long', int32_t: 'int', float: 'double', Float: 'double' };
    name = NORMAL[name] || name;
    const ty = { k: 'type', name, args: [], ptr: 0, ref: false, dims: 0, line: t.line };
    if (this.isOp('<')) {
      this.next();
      if (!this.atCloseAngle()) {
        for (;;) {
          if (this.tok.t === 'num') ty.args.push({ k: 'num', value: this.next().v });
          else ty.args.push(this.parseType());
          if (!this.accept(',')) break;
        }
      }
      if (!this.closeAngle()) throw new ParseError('Expected ">"', this.tok.line);
    }
    return ty;
  }

  parseArgs() {
    this.expect('(');
    const args = [];
    while (!this.isOp(')')) {
      args.push(this.isOp('{') ? this.initList() : this.parseAssign());
      if (!this.accept(',')) break;
    }
    this.expect(')');
    return args;
  }

  parsePostfix() {
    let e = this.parsePrimary();
    for (;;) {
      const t = this.tok;
      if (t.t !== 'op') break;
      const line = t.line;
      if (t.v === '(') { e = { k: 'call', callee: e, args: this.parseArgs(), line }; continue; }
      if (t.v === '[') { this.next(); const idx = this.parseExpr(); this.expect(']'); e = { k: 'index', obj: e, index: idx, line }; continue; }
      if (t.v === '.' || t.v === '->') {
        this.next();
        if (this.isId('template')) this.next();
        if (this.isOp('<') && this.lang === 'java') this.skipAngles(); // explicit generic call: Collections.<Integer>emptyList()
        const name = this.tok.t === 'id' ? this.next().v : (this.fail('Expected a member name'));
        // explicit template args on method call:  v.template foo<int>(...)  -- rare; skip
        e = { k: 'member', obj: e, name, arrow: t.v === '->', line };
        continue;
      }
      if (t.v === '++' || t.v === '--') { this.next(); e = { k: 'postinc', op: t.v, expr: e, line }; continue; }
      if (t.v === '::' && this.peekAt().t === 'id') { this.next(); const name = this.next().v; e = { k: 'scope', left: e, name, line }; continue; }
      break;
    }
    return e;
  }

  parsePrimary() {
    const t = this.tok;
    const line = t.line;
    switch (t.t) {
      case 'num': this.next(); return { k: 'num', value: t.v, kind: t.kind, line };
      case 'str': { this.next(); let s = t.v; while (this.tok.t === 'str') s += this.next().v; return { k: 'str', value: s, line }; }
      case 'chr': this.next(); return { k: 'chr', value: t.v, line };
      case 'op':
        if (t.v === '(') {
          this.next();
          const e = this.parseExpr();
          this.expect(')');
          return { k: 'paren', expr: e, line };
        }
        if (t.v === '[' && this.lang === 'cpp') return this.cppLambda();
        if (t.v === '{') return this.initList();
        if (t.v === '::') { this.next(); return this.parsePrimary(); }
        break;
      case 'id': {
        if (t.v === 'std' && this.peekAt().v === '::' && this.peekAt(2).t === 'id') { this.next(); this.next(); return this.parsePrimary(); }
        if (t.v === 'true' || t.v === 'false') { this.next(); return { k: 'bool', value: t.v === 'true', line }; }
        if (t.v === 'nullptr' || t.v === 'NULL' || t.v === 'null') { this.next(); return { k: 'null', line }; }
        if (t.v === 'this') { this.next(); return { k: 'this', line }; }
        if (this.lang === 'java' && this.isLambdaAhead()) return this.javaLambda();
        // type-ish expression: static_cast<T>(x), vector<int>(n), make_pair<..>(), max<int>(..), int(x)
        if (/^(static_cast|dynamic_cast|reinterpret_cast|const_cast)$/.test(t.v) && this.peekAt().v === '<') {
          this.next(); this.next();
          const ty = this.parseType();
          this.closeAngle();
          this.expect('(');
          const e = this.parseExpr();
          this.expect(')');
          return { k: 'cast', type: ty, expr: e, line };
        }
        if (this.prims.has(t.v) && this.peekAt().v === '(' && !['void', 'auto', 'var'].includes(t.v)) { // functional cast: int(x), string(3,'a')
          const ty = this.parseType();
          const args = this.parseArgs();
          return { k: 'construct', type: ty, args, line };
        }
        if (['unsigned', 'long', 'short', 'signed'].includes(t.v)) { const ty = this.parseType(); if (this.isOp('(')) return { k: 'construct', type: ty, args: this.parseArgs(), line }; return { k: 'typeexpr', type: ty, line }; }
        // Ident<...> followed by ( { or ::   => template-id
        if (this.peekAt().v === '<' && !this.templateParams.has(t.v)) {
          const save = this.save();
          try {
            const ty = this.parseType();
            if (this.isOp('(') ) return { k: 'construct', type: ty, args: this.parseArgs(), line };
            if (this.isOp('{') && ty.args.length) { const il = this.initList(); return { k: 'construct', type: ty, args: il.items, brace: true, line }; }
            if (this.isOp('::') && ty.args.length) return { k: 'typeexpr', type: ty, line };
          } catch (e) { if (!(e instanceof ParseError)) throw e; }
          this.restore(save);
        }
        this.next();
        return { k: 'id', name: t.v, line };
      }
      default: break;
    }
    throw new ParseError(`Unexpected "${t.v}"`, t.line);
  }
}
