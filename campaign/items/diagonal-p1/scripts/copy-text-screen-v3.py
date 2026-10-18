"""Text-level copy screen for retrofit deliveries, v3 (declaration-keyed).

Identical to audits/evidence/retrofit/copy-text-screen-v2.py except in how declarations are told
apart. v2 skipped a pair when (path, extracted name) coincided, so two distinct declarations in one
file with the same short name were never compared: the same name in two namespaces (a generic
`DiagSimulator.time_hierarchy_of_pos` beside the received `Complexity.time_hierarchy_of_pos`, both
written `theorem time_hierarchy_of_pos`), or two anonymous instances (Diagonal Part 1 gate, m2).
v3 identifies each declaration by its path and source position and skips a pair only when both
sides are the same declaration. Labels: as in v2 (`<file>::<name>`) when the extracted name is
unique among the file's screened declarations; otherwise the namespace-qualified name, with `#k`
appended (k-th in source order) when that is still not unique. Namespaces are tracked through
`namespace`, `section`, `noncomputable section`, `mutual` and `end`; a dotted `namespace A.B`
opens two scopes, as in Lean, and `_root_.` is honoured. Hence, when no file in the argument list
has two screened declarations with the same extracted name, v3's output is byte-identical to
v2's. An `end` that closes no matching scope stops the screen (exit 1, message on stderr).

For the given Lean files it lists every like-kind pair (proof vs proof, term vs term) in which one
declaration reproduces at least half of another's extracted body (at least 60 characters, greedy
tiling with blocks of at least 25), within a file and across the given files. It also prints the
total reproduced text. Run it before and after a change: a pair present after but not before is
new duplication; inlining a deleted copy into a consumer shows up as such a pair.
Usage: python3 -I copy-text-screen-v3.py <repo-root> <file.lean> [<file.lean> ...]
"""
import os, re, sys
root, files = sys.argv[1], sys.argv[2:]
paths = list(dict.fromkeys(os.path.normpath(f) for f in files))
nbase = {}
for p in paths: nbase[os.path.basename(p)] = nbase.get(os.path.basename(p), 0) + 1
label = lambda p: os.path.basename(p) if nbase[os.path.basename(p)] == 1 else p
def strip(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
SCOPE = re.compile(r"^[ \t]*(?:(namespace)[ \t]+(\S+)|(?:noncomputable[ \t]+)?(section)\b[ \t]*([^\s]*)"
                   r"|(mutual)\b|(end)\b[ \t]*([^\s]*))", re.M)
def scopes(p, t):
    """(offset, namespace) after each scope command of the stripped text `t`, in source order."""
    stack = []; ev = [(0, '')]
    for m in SCOPE.finditer(t):
        if m.group(1): stack += [('namespace', c) for c in m.group(2).split('.')]
        elif m.group(3): stack.append(('section', m.group(4)))
        elif m.group(5): stack.append(('mutual', ''))
        else:  # `end A.B` closes the innermost scopes B, then A; a bare `end` an anonymous one
            for c in reversed(m.group(7).split('.')):
                if not stack or stack[-1][1] != c:
                    sys.exit(f"copy-text-screen-v3: {p}:{t.count(chr(10), 0, m.start()) + 1}: "
                             f"`end {m.group(7)}` does not close {stack[-1] if stack else 'any scope'}")
                stack.pop()
        ev.append((m.end(), '.'.join(n for k, n in stack if k == 'namespace')))
    return ev
def qualify(ns, name):
    if name.startswith('_root_.'): return name[len('_root_.'):]
    return f'{ns}.{name}' if ns else name
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
def lcs(a, b):
    lo, hi, best = 0, min(len(a), len(b)), ''
    while lo < hi:
        mid = (lo + hi + 1) // 2
        subs = {b[i:i + mid] for i in range(len(b) - mid + 1)}
        hit = next((a[i:i + mid] for i in range(len(a) - mid + 1) if a[i:i + mid] in subs), None)
        if hit is not None: lo, best = mid, hit
        else: hi = mid - 1
    return lo, best
def tiled(a, b):
    c = 0
    while True:
        n, seg = lcs(a, b)
        if n < 25: return c
        c += n; a = a.replace(seg, '\x00', 1); b = b.replace(seg, '\x01', 1)
grams = lambda x: {x[i:i + 25] for i in range(len(x) - 24)}
decls = []
for p in paths:
    t = strip(open(f'{root}/{p}', encoding='utf-8').read()); ms = list(DECL.finditer(t))
    ev = scopes(p, t); found = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        kind = 'proof' if m.group(2) in ('theorem', 'lemma') else 'term'
        bd = re.sub(r'\s+', '', body(t[m.start():end]))
        ns = [n for o, n in ev if o <= m.start()][-1]
        if len(bd) >= 60: found.append((m.start(), m.group(3), qualify(ns, m.group(3)), kind, bd))
    short = {}; qual = {}
    for (_, nm, qn, _, _) in found: short[nm] = short.get(nm, 0) + 1; qual[qn] = qual.get(qn, 0) + 1
    seen = {}
    for (pos, nm, qn, kind, bd) in found:
        if short[nm] == 1: name = nm
        elif qual[qn] == 1: name = qn
        else: seen[qn] = seen.get(qn, 0) + 1; name = f'{qn}#{seen[qn]}'
        decls.append(((p, pos), name, kind, bd, grams(bd)))
pairs = []; total = 0
for (fa, a, ka, ta, ga) in decls:
    for (fb, b, kb, tb, gb) in decls:
        if fa == fb or ka != kb or not (ga & gb): continue
        sh = tiled(tb, ta)
        if sh >= 60 and 2 * sh >= len(tb):
            pairs.append((sh / len(tb), sh, len(tb), f'{label(fa[0])}::{a}', f'{label(fb[0])}::{b}')); total += sh
pairs.sort(reverse=True)
print(f"declarations screened: {len(decls)}; copy pairs (target reproduces >= half of source): {len(pairs)}; reproduced text: {total:,} chars")
for frac, sh, ln, a, b in pairs:
    print(f"   {a}  reproduces  {b}: {sh}/{ln} = {frac:.0%}")
