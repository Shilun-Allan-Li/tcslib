#!/usr/bin/env python3
"""headercheck.py <brief.md> <decls2.py> <head-checkout> <targets.tsv>   (cleanup-stage1, check 3)

Compares the header of every target as written in the brief's ```lean blocks with the header of the
declaration at the head, both normalized by decls2's own parser (comments stripped, statement cut at
the top-level `:=`, `where`, or the first equation arm; whitespace collapsed).  Prints PASS per
target or the two texts; RESULT line at the end.  The brief's trailing `-- S1-xx`/source comments
are comments and are stripped like any comment.  Each block is split at every line that starts a
declaration, since the brief lists bodiless headers back to back.
"""
import importlib.util, re, sys, types

brief, d2, head, tsv = sys.argv[1:5]
src = open(d2, encoding='utf-8').read()
src = src.split('\nfor f in files:', 1)[0]              # the parser only, not the CLI loop
mod = types.ModuleType('decls2'); mod.__dict__['sys'] = types.SimpleNamespace(argv=['', '', ''])
code = src.replace('root, base = sys.argv[1], sys.argv[2]', 'root, base = None, None') \
          .replace('files = sys.argv[3:]', 'files = []')
exec(compile(code, 'decls2.py', 'exec'), mod.__dict__)
decls = mod.decls
T = [l.rstrip('\n').split('\t') for l in open(tsv) if l.strip()]
text = open(brief, encoding='utf-8').read()
blocks = re.findall(r'```lean\n(.*?)```', text, flags=re.S)
# parse the brief's blocks as one pseudo-file per block (no namespace: names are short or dotted)
bdecls = {}
KWL = re.compile(r'^(?:protected |noncomputable |private )*(?:theorem|lemma|def|abbrev) ')
for b in blocks:
    chunks, cur = [], []
    for l in b.split('\n'):
        if KWL.match(l) and cur:
            chunks.append('\n'.join(cur)); cur = []
        cur.append(l)
    chunks.append('\n'.join(cur))
    for ch in chunks:
        for full, (kind, line, stmt) in decls(ch).items():
            bdecls[full] = stmt
norm = lambda s: re.sub(r'\s+', ' ', s).strip()
heads = {}
for tid, full, kind, P, path in T:
    if path not in heads:
        try:
            heads[path] = decls(open(f"{head}/{path}", encoding="utf-8").read())
        except FileNotFoundError:
            heads[path] = {}
npass = 0
for tid, full, kind, P, path in T:
    hs = heads[path].get(full)
    # the brief names the declaration by its written name (short, dotted, or _root_-prefixed)
    cands = [k for k in bdecls if full == k or full.endswith('.' + k)]
    if not hs or not cands:
        print(f'MISSING\t{tid}\t{full}\thead={bool(hs)}\tbrief={cands}'); continue
    k = max(cands, key=len)
    bs = norm(bdecls[k]); hh = norm(hs[2])
    # the head writes the declared name as in the brief; compare the texts as written
    if bs == hh:
        npass += 1; print(f'PASS\t{tid}\t{full}')
    else:
        print(f'DIFF\t{tid}\t{full}\n    brief: {bs}\n    head:  {hh}')
print(f'RESULT {npass}/{len(T)} headers equal to the brief')
