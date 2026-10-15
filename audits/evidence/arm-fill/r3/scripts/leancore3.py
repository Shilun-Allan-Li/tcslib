"""Shared primitives for the round-3 scripts, consistent with copy-text-screen-v3.py.

strip_keep_lines: nesting-aware comment removal that keeps newlines (line numbers survive).
decls(path, text): the declarations v3 screens (body >= 60 whitespace-free characters), with v3's
own labels (short name if unique among the file's screened declarations, else the namespace-
qualified name, else `#k`), the header line, the span's last line, code lines and body size.
alldecls(path, text): the same over every declaration (no floor), for the all-body denominator.
The comment strip used for the screen's bodies is v3's (which drops newlines inside comments); the
line-keeping strip is used only for positions, and both give the same declaration texts modulo
whitespace, which the body measure removes.
"""
import re
def strip_keep_lines(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == '\n': out.append('\n')
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            if j < 0: break
            i = j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
SCOPE = re.compile(r"^[ \t]*(?:(namespace)[ \t]+(\S+)|(?:noncomputable[ \t]+)?(section)\b[ \t]*([^\s]*)"
                   r"|(mutual)\b|(end)\b[ \t]*([^\s]*))", re.M)
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (ch == '|' or re.match(r'\bwhere\b', b[i:i + 6])): return b[i:]
    return ''
def scopes(t):
    stack = []; ev = [(0, '')]
    for m in SCOPE.finditer(t):
        if m.group(1): stack += [('namespace', c) for c in m.group(2).split('.')]
        elif m.group(3): stack.append(('section', m.group(4)))
        elif m.group(5): stack.append(('mutual', ''))
        else:
            for c in reversed(m.group(7).split('.')):
                if not stack or stack[-1][1] != c: raise ValueError('unbalanced end')
                stack.pop()
        ev.append((m.end(), '.'.join(n for k, n in stack if k == 'namespace')))
    return ev
def qualify(ns, name):
    if name.startswith('_root_.'): return name[len('_root_.'):]
    return f'{ns}.{name}' if ns else name
def _scan(text, floor):
    t = strip_keep_lines(text); ms = list(DECL.finditer(t)); ev = scopes(t); found = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        seg = t[m.start():end]
        bd = re.sub(r'\s+', '', body(seg))
        ns = [n for o, n in ev if o <= m.start()][-1]
        l0 = t.count('\n', 0, m.start()) + 1
        l1 = l0 + seg.rstrip().count('\n')
        cl = sum(1 for l in seg.split('\n') if l.strip())
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        if len(bd) >= floor:
            found.append(dict(short=m.group(3), qual=qualify(ns, m.group(3)), kind=kind, l0=l0, l1=l1,
                              code=cl, chars=len(bd), private='private' in m.group(1), body=bd))
    short = {}; qual = {}
    for d in found: short[d['short']] = short.get(d['short'], 0) + 1; qual[d['qual']] = qual.get(d['qual'], 0) + 1
    seen = {}
    for d in found:
        if short[d['short']] == 1: d['name'] = d['short']
        elif qual[d['qual']] == 1: d['name'] = d['qual']
        else: seen[d['qual']] = seen.get(d['qual'], 0) + 1; d['name'] = f"{d['qual']}#{seen[d['qual']]}"
    return found, t
def decls(text): return _scan(text, 60)[0]
def alldecls(text): return _scan(text, 0)[0]
def code_lines(text): return sum(1 for l in strip_keep_lines(text).split('\n') if l.strip())
