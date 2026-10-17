"""Fully qualified names of the declarations of Lean files (namespace tracking on the
comment-stripped text; `protected`/`private` noted). Resolves a list of wanted names.
usage: python3 -I qualnames.py <root> <files.txt> <wanted.txt>
Prints, for each wanted fully qualified name, the declaring file (module) and line, or MISSING;
ambiguous matches are reported.
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanlib import strip_keep_lines, DECL

root, flist, wanted = sys.argv[1:4]
NS = re.compile(r'^namespace\s+(\S+)'); SEC = re.compile(r'^(noncomputable\s+)?section\b\s*(\S*)')
END = re.compile(r'^end\b\s*(\S*)')
index = {}
for f in [l.strip() for l in open(flist) if l.strip()]:
    s = strip_keep_lines(open(os.path.join(root, f), encoding='utf-8').read())
    stack = []  # entries: ('ns', parts) or ('sec', name)
    for ln, l in enumerate(s.split('\n'), 1):
        m = NS.match(l)
        if m: stack.append(('ns', m.group(1).split('.'))); continue
        m = SEC.match(l)
        if m: stack.append(('sec', m.group(2))); continue
        if re.match(r'^mutual\b', l): stack.append(('mut', '')); continue
        m = END.match(l)
        if m and stack: stack.pop(); continue
        m = DECL.match(l)
        if m and m.group(3):
            ns = [p for k, v in stack if k == 'ns' for p in v]
            name = m.group(3)
            full = name[1:] if name.startswith('_root_.') else '.'.join(ns + [name])
            index.setdefault(full, []).append((f, ln, 'private' in m.group(1).split()))
ok = True
for w in [l.strip() for l in open(wanted) if l.strip() and not l.startswith('#')]:
    hits = index.get(w, [])
    if len(hits) == 1:
        f, ln, priv = hits[0]
        print(f'{w}\t{f[:-5].replace("/", ".")}\t{ln}' + ('\tPRIVATE' if priv else ''))
        if priv: ok = False
    else:
        ok = False
        print(f'{w}\t{"MISSING" if not hits else "AMBIGUOUS " + str(hits)}')
print('ALL RESOLVED, all public' if ok else 'PROBLEMS ABOVE')
