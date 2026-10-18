"""Duplication ledger from a copy-text screen output over the flattened population.
usage: python3 -I ledger.py <screen.out> <labels.tsv> <added.txt> <screen-root> <disclosed.tsv>
labels.tsv: flat-label TAB repo-path TAB sha256.  disclosed.tsv: family TAB repo-path::decl
(copy side) TAB repo-path::decl (original side); a pair is disclosed when its two sides are
the two sides of a listed family (either direction).
Declaration spans are recomputed with the screen's own declaration regex on a comment-stripped
text that keeps line structure; a span runs from its header line to the line before the next
header. Body characters are the screen's measure (whitespace-free body after the first
depth-0 `:=`, or the `|`/`where` part).
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanlib import strip_keep_lines

out, labels, added, sroot, disc = sys.argv[1:6]
lab = {}
for l in open(labels, encoding='utf-8'):
    a, p, _ = l.rstrip('\n').split('\t'); lab[a] = p
new = {l.strip() for l in open(added) if l.strip()}
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
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
spans = {}; fileinfo = {}
for flat, path in lab.items():
    t = strip_keep_lines(open(os.path.join(sroot, flat), encoding='utf-8').read())
    ms = list(DECL.finditer(t)); total_chars = 0
    code_lines = sum(1 for l in t.split('\n') if l.strip())
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        seg = t[m.start():end]
        bd = re.sub(r'\s+', '', body(seg))
        l0 = t.count('\n', 0, m.start()) + 1
        l1 = l0 + seg.rstrip().count('\n')
        cl = sum(1 for l in seg.split('\n') if l.strip())
        if len(bd) >= 60: total_chars += len(bd)
        spans.setdefault((path, m.group(3)), []).append((l0, l1, cl, len(bd), 'private' in m.group(1)))
    raw = open(os.path.join(sroot, flat), encoding='utf-8').read().split('\n')
    fileinfo[path] = dict(chars=total_chars, code=code_lines, lines=len(raw) - (1 if raw[-1] == '' else 0))
fams = []
for l in open(disc, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    fam, a, b = l.rstrip('\n').split('\t'); fams.append((fam, a, b))
def family(x, y):
    for fam, a, b in fams:
        if {x, y} == {a, b}: return fam
    return None
P = re.compile(r'^\s+(\S+?)::(\S+)\s+reproduces\s+(\S+?)::(\S+): (\d+)/(\d+) = (\d+)%')
rows = []; infile_new = 0
for l in open(out, encoding='utf-8'):
    m = P.match(l)
    if not m: continue
    fa, a, fb, b, sh, ln, pct = m.groups()
    pa, pb = lab[fa], lab[fb]
    if pa == pb:
        if pa in new: infile_new += 1
        continue
    if pa not in new and pb not in new: continue
    rows.append((pa, a, pb, b, int(sh), int(ln), int(pct)))
def span(p, n):
    s = spans.get((p, n), [])
    return s[0] if len(s) == 1 else (s[0] if s else None), len(s)
print(f'cross-file pairs with at least one side in an added file: {len(rows)}; '
      f'in-file pairs inside added files (not listed): {infile_new}')
kinds = {'new<-lib': 0, 'lib<-new': 0, 'new<->new': 0}
copy_side = {}   # (path, decl) -> list of reasons
print('\n## Pairs (copy side = the declaration that reproduces at least half of the other)')
print('class | copy side (file:lines) | source side (file:lines) | shared/source chars = % | disclosure')
for pa, a, pb, b, sh, ln, pct in rows:
    if pa in new and pb not in new: cls = 'new<-lib'
    elif pa not in new and pb in new: cls = 'lib<-new'
    else: cls = 'new<->new'
    kinds[cls] += 1
    fam = family(f'{pa}::{a}', f'{pb}::{b}')
    (sa, na), (sb, nb) = span(pa, a), span(pb, b)
    ra = f'{sa[0]}-{sa[1]}' if sa else '?'; rb = f'{sb[0]}-{sb[1]}' if sb else '?'
    amb = '' if na == 1 and nb == 1 else f' [name occurs {na}/{nb} times]'
    print(f'{cls} | {pa}:{ra} {a} | {pb}:{rb} {b} | {sh}/{ln} = {pct}% | '
          f'{"DISCLOSED (" + fam + ")" if fam else "undisclosed"}{amb}')
    if pa in new: copy_side.setdefault((pa, a), []).append((pb, b, fam, cls, sh))
    if cls == 'lib<-new' and pb in new: copy_side.setdefault((pb, b), []).append((pa, a, fam, 'reverse', sh))
print('\npair classes:', kinds)
# per-file ledger: copy-side declarations of each added file (each counted once)
print('\n## Per-file ledger (added files): declarations that reproduce >= half of a declaration in '
      'another file of the population; whole bodies counted once')
print('file | lines | code lines | body chars | copy decls | copy code lines | copy body chars | '
      'share (chars) | share (code lines) | of which vs library | disclosed | shared-text measure')
tot = dict(lines=0, code=0, chars=0, cdecl=0, ccode=0, cchars=0, libchars=0, libcode=0, disc_chars=0)
over = []
for p in sorted(new):
    fi = fileinfo.get(p)
    if not fi: continue
    ds = [(k, v) for k, v in copy_side.items() if k[0] == p]
    cc = sum(span(*k)[0][2] for k, _ in ds if span(*k)[0]); ch = sum(span(*k)[0][3] for k, _ in ds if span(*k)[0])
    lib = [(k, v) for k, v in ds if any(r[3] in ('new<-lib',) or (r[0] not in new) for r in v)]
    lch = sum(span(*k)[0][3] for k, _ in lib if span(*k)[0]); lcl = sum(span(*k)[0][2] for k, _ in lib if span(*k)[0])
    dch = sum(span(*k)[0][3] for k, v in ds if span(*k)[0] and all(r[2] for r in v))
    shr = sum(min(span(*k)[0][3], max(r[4] for r in v)) for k, v in ds if span(*k)[0])
    tot['shared'] = tot.get('shared', 0) + shr
    for key, val in (('lines', fi['lines']), ('code', fi['code']), ('chars', fi['chars']), ('cdecl', len(ds)),
                     ('ccode', cc), ('cchars', ch), ('libchars', lch), ('libcode', lcl), ('disc_chars', dch)):
        tot[key] += val
    shc = ch / fi['chars'] if fi['chars'] else 0; shl = cc / fi['code'] if fi['code'] else 0
    if ds:
        print(f'{p} | {fi["lines"]} | {fi["code"]} | {fi["chars"]} | {len(ds)} | {cc} | {ch} | '
              f'{shc:.2%} | {shl:.2%} | {lch} chars | {dch} chars | shared text {shr} chars = {shr/fi["chars"]:.2%}')
    if shc > 0.2 or shl > 0.2: over.append((p, shc, shl, shr / fi['chars'] if fi['chars'] else 0))
print(f'TOTAL over the 73 added files: {tot["lines"]} lines, {tot["code"]} code lines, {tot["chars"]} body chars; '
      f'copy-side declarations {tot["cdecl"]}, {tot["ccode"]} code lines ({tot["ccode"]/tot["code"]:.2%}), '
      f'{tot["cchars"]} body chars ({tot["cchars"]/tot["chars"]:.2%}); of which reproducing library '
      f'declarations: {tot["libcode"]} code lines, {tot["libchars"]} chars ({tot["libchars"]/tot["chars"]:.2%}); '
      f'all-disclosed copy declarations: {tot["disc_chars"]} chars; shared-text measure (per copy declaration, the largest overlap with one source, capped at its body): {tot.get("shared",0)} chars ({tot.get("shared",0)/tot["chars"]:.2%})')
print('\nfiles above one fifth by the whole-body measure (chars or code lines), with their shared-text share:')
for p, a, b, c in over: print(f'  {p}: whole-body {a:.1%} of chars, {b:.1%} of code lines; shared text {c:.1%}')
print('files above one fifth by the shared-text measure:', [p for p, a, b, c in over if c > 0.2] or 'none')
# Copies of existing (library) material only: copy-side declarations of added files that
# reproduce, or are reproduced by, a declaration of a library file; split by disclosure.
print('\n## Copies of existing library material (the policy\'s "duplicated proved material")')
libk = {k: [r for r in v if r[0] not in new] for k, v in copy_side.items()}
libk = {k: v for k, v in libk.items() if v}
def meas(keys):
    wb = sum(span(*k)[0][3] for k in keys if span(*k)[0]); cl = sum(span(*k)[0][2] for k in keys if span(*k)[0])
    sh = sum(min(span(*k)[0][3], max(r[4] for r in libk[k])) for k in keys if span(*k)[0])
    return len(keys), cl, wb, sh
copyside_disc = {tuple(a.split('::', 1)) for _, a, _ in fams}
disc = [k for k in libk if k in copyside_disc]
undisc = [k for k in libk if k not in copyside_disc]
for lab, ks in (('all', list(libk)), ('disclosed (the declaration is a listed copy side)', disc), ('undisclosed (not a listed copy side)', undisc)):
    n, cl, wb, sh = meas(ks)
    print(f'{lab}: {n} declarations, {cl} code lines ({cl/tot["code"]:.2%}), whole bodies {wb} chars ({wb/tot["chars"]:.2%}), shared text {sh} chars ({sh/tot["chars"]:.2%})')
print('per file (library copies only): file | decls | code lines | whole-body chars (share) | shared chars (share)')
for p in sorted(new):
    ks = [k for k in libk if k[0] == p]
    if not ks: continue
    n, cl, wb, sh = meas(ks); fi = fileinfo[p]
    print(f'  {p} | {n} | {cl} | {wb} ({wb/fi["chars"]:.1%}) | {sh} ({sh/fi["chars"]:.1%})')
print('\n## The disclosed families, member by member (copy side and original; the screen pair, if any)')
pairmap = {}
for pa, a, pb, b, sh, ln, pct in rows:
    pairmap.setdefault((pa, a, pb, b), []).append(f'{sh}/{ln} = {pct}%')
for fam, a, b in fams:
    pa, na = a.split('::', 1); pb, nb = b.split('::', 1)
    sa, sb = span(pa, na)[0], span(pb, nb)[0]
    found = pairmap.get((pa, na, pb, nb), []) + [x + ' (reverse)' for x in pairmap.get((pb, nb, pa, na), [])]
    ra = f'{sa[0]}-{sa[1]} ({sa[2]} code lines)' if sa else 'span not found (body under 60 chars or not matched)'
    rb = f'{sb[0]}-{sb[1]}' if sb else 'span not found'
    print(f'  {fam}: {pa}:{ra} {na}  <-  {pb}:{rb} {nb}  | screen: {", ".join(found) or "no pair at the threshold"}')
print('undisclosed library copy-side declarations, largest shared text first:')
for k in sorted(undisc, key=lambda k: -max(r[4] for r in libk[k])):
    s0 = span(*k)[0]
    srcs = '; '.join(f'{q}::{b} ({shc} shared)' for q, b, f, _, shc in libk[k] if not f)
    print(f'  {k[0]}:{s0[0]}-{s0[1]} {k[1]} ({s0[2]} code lines, {s0[3]} chars) <- {srcs}')

if len(sys.argv) > 6:
    # Net view of the internal (added <-> added) families: connected components of the
    # undirected pair graph among added-file declarations; the member in the module that is
    # earliest in the global topological import order counts as the original, the rest as copies.
    order = {l.strip() + '.lean': i for i, l in enumerate(open(sys.argv[6])) if l.strip()}
    adj = {}
    for pa, a, pb, b, sh, ln, pct in rows:
        if pa in new and pb in new:
            adj.setdefault((pa, a), set()).add((pb, b)); adj.setdefault((pb, b), set()).add((pa, a))
    seen = set(); comps = []
    for v in adj:
        if v in seen: continue
        st = [v]; comp = []
        seen.add(v)
        while st:
            u = st.pop(); comp.append(u)
            for w in adj[u]:
                if w not in seen: seen.add(w); st.append(w)
        comps.append(comp)
    libcopies = {k for k, v in copy_side.items() if any(r[0] not in new for r in v)}
    net = set(libcopies)
    print(f'\n## Net view: {len(comps)} internal families among added files (connected components)')
    for comp in sorted(comps, key=lambda c: -len(c)):
        comp.sort(key=lambda k: (order.get(k[0], 10**9), span(*k)[0][0] if span(*k)[0] else 0))
        orig = comp[0]; net.update(comp[1:])
        names = ', '.join(f'{k[0].split("/")[-2]}/{k[0].split("/")[-1][:-5]}::{k[1]}' for k in comp)
        print(f'  {len(comp)} members; original taken as {orig[0]}::{orig[1]}: {names}')
    nch = sum(span(*k)[0][3] for k in net if span(*k)[0]); ncl = sum(span(*k)[0][2] for k in net if span(*k)[0])
    nsh = sum(min(span(*k)[0][3], max(r[4] for r in copy_side.get(k, [(0, 0, 0, 0, 0)]))) for k in net if span(*k)[0])
    print(f'NET copied material over the 73 added files: {len(net)} declarations, {ncl} code lines '
          f'({ncl/tot["code"]:.2%} of {tot["code"]}), {nch} body chars ({nch/tot["chars"]:.2%} of {tot["chars"]}); '
          f'shared-text measure {nsh} chars ({nsh/tot["chars"]:.2%})')
    print('NET per file (files with any):')
    for p in sorted(new):
        ks = [k for k in net if k[0] == p]
        if not ks: continue
        c1 = sum(span(*k)[0][3] for k in ks if span(*k)[0]); c2 = sum(span(*k)[0][2] for k in ks if span(*k)[0])
        fi = fileinfo[p]
        print(f'  {p}: {len(ks)} decls, {c2} code lines ({c2/fi["code"]:.1%}), {c1} chars ({c1/fi["chars"]:.1%})')
print('\n## Copy-side declarations of added files, with every source they reproduce')
for (p, a), v in sorted(copy_side.items()):
    s = span(p, a)[0]
    srcs = '; '.join(f'{q}::{b} ({f or "undisclosed"}, {shc} shared)' for q, b, f, _, shc in v)
    print(f'{p}:{s[0]}-{s[1]} {a} ({s[2]} code lines, {s[3]} chars) <- {srcs}')
