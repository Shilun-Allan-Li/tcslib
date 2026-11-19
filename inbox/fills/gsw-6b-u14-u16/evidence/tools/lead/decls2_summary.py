#!/usr/bin/env python3
"""Summary of decls2.py on the owned file: runs the records' decls2.py (unchanged) and counts its
ADDED/CHANGED/REMOVED rows, and lists the public declarations its parser sees at the base and in
the working tree (by importing its `decls` function), so that an empty diff is shown to be over a
non-empty set. Usage: python3 -I decls2_summary.py <root> <base> <decls2.py> <file>"""
import sys, subprocess, importlib.util, io, contextlib
root, base, tool, f = sys.argv[1:5]
out = subprocess.run(['python3', '-I', tool, root, base, f], capture_output=True, text=True)
rows = [l for l in out.stdout.split('\n') if l.strip()]
cnt = {k: sum(1 for l in rows if l.startswith(k + '\t')) for k in ('ADDED', 'CHANGED', 'REMOVED')}
src = open(tool).read().split('\nfor f in files:')[0]
g = {'__name__': 'decls2_lib'}
sys_argv = sys.argv
sys.argv = ['decls2', root, base]
exec(compile(src, tool, 'exec'), g)
sys.argv = sys_argv
old = subprocess.run(['git', 'show', f'{base}:{f}'], cwd=root, capture_output=True, text=True).stdout
new = open(f'{root}/{f}', encoding='utf-8').read()
a, b = g['decls'](old), g['decls'](new)
print(f'decls2.py rc={out.returncode}; rows: ADDED {cnt["ADDED"]}, CHANGED {cnt["CHANGED"]}, REMOVED {cnt["REMOVED"]}')
print(f'public declarations parsed: base {len(a)}, head {len(b)}; identical statements: '
      f'{sum(1 for n in a if n in b and a[n][2] == b[n][2])}')
for n in sorted(b):
    print(f'{b[n][0]}\t{n}\tbase line {a[n][1] if n in a else "-"}\thead line {b[n][1]}')
