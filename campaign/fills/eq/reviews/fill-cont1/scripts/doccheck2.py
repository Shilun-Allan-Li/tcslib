"""Docstrings and proof sketches of the declarations in head lines [a, b] (python3 -I).
A declaration starts at a line matching DECL (outside comments); its docstring is the `/-- … -/`
block ending on the line before it (attributes allowed between); its length runs to the line
before the next declaration's docstring or declaration, or to b.  A proof over 20 lines must carry
a literal `**Proof sketch.**` in its docstring (policy.md §3).
usage: python3 -I doccheck2.py <file> <a> <b>"""
import re, sys
f, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
L = open(f, encoding='utf-8').read().split('\n')
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)")
# comment depth per line start
depth = 0; starts = []; dstart = {}
open_doc = None; docs = []  # (start, end) of /-- … -/ blocks
for i, l in enumerate(L):
    starts.append(depth); j = 0
    while j < len(l):
        if l.startswith('/--', j) and depth == 0: open_doc = i; depth += 1; j += 3; continue
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth: depth -= 1; j += 2
        else: j += 1; continue
        if depth == 0 and open_doc is not None: docs.append((open_doc, i)); open_doc = None
decls = [(i, m.group(1).strip(), m.group(2), m.group(3)) for i, l in enumerate(L)
         if a - 1 <= i <= b - 1 and starts[i] == 0 and (m := DECL.match(l))]
docend = {e: s for s, e in docs}
rows = []; nodoc = []; nosketch = []
for k, (i, mods, kw, name) in enumerate(decls):
    d = docend.get(i - 1)
    doc = '\n'.join(L[d:i]) if d is not None else ''
    nxt = decls[k + 1][0] if k + 1 < len(decls) else b
    # the next declaration's docstring start, if any
    nd = next((s for s, e in docs if e == nxt - 1), None) if k + 1 < len(decls) else None
    end = (nd if nd is not None else nxt) - 1
    while end > i and not L[end].strip(): end -= 1
    n = end - i + 1
    sk = '**Proof sketch.**' in doc
    rows.append((i + 1, mods, kw, name, n, d is not None, sk))
    if d is None: nodoc.append((i + 1, kw, name))
    if n > 20 and kw in ('theorem', 'lemma', 'def', 'instance', 'abbrev') and not sk: nosketch.append((i + 1, kw, name, n))
print(f'declarations in lines {a}-{b}: {len(rows)}; non-private: {[r[3] for r in rows if "private" not in r[1]]}')
print('without a docstring:', nodoc if nodoc else 'none')
print('over 20 lines without a literal "**Proof sketch.**":', nosketch if nosketch else 'none')
print('over 20 lines:', sum(r[4] > 20 for r in rows), '; with a sketch:', sum(r[4] > 20 and r[6] for r in rows))
big = sorted(rows, key=lambda r: -r[4])[:15]
print('largest:'); [print(f'   {r[0]} {r[2]} {r[3]}: {r[4]} lines, sketch {r[6]}') for r in big]
# proof length: lines after the line that opens the proof (`:= by` or a line ending `:=`)
print('## theorems: proof lines (after the statement) over 20 without a sketch')
cnt = 0
for k, (i, mods, kw, name) in enumerate(decls):
    if kw not in ('theorem', 'lemma'): continue
    r = rows[k]; end = i + r[4] - 1
    p = next((j for j in range(i, end + 1) if re.search(r':=\s*by\b|:=\s*$', L[j])), None)
    if p is None: continue
    n = end - p
    if n > 20: cnt += 1
    if n > 20 and not r[6]: print(f'   {i + 1} {name}: proof {n} lines, NO sketch')
print('theorems with proofs over 20 lines:', cnt)
