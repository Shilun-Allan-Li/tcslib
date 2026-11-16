"""doconly.py <worktree> <rev> <file>...: check that the working-tree change of each file against <rev> is
docstring-only: with every `/-- … -/` doc comment removed, the two texts are byte-identical; also reports
the changed docstrings' count and the max line width (Python len) of the new file."""
import sys, re, subprocess
wt, rev, files = sys.argv[1], sys.argv[2], sys.argv[3:]
strip = lambda s: re.sub(r'/--.*?-/', '/--DOC-/', s, flags=re.S)
docs = lambda s: re.findall(r'/--.*?-/', s, flags=re.S)
ok = True
for f in files:
    old = subprocess.run(['git', '-C', wt, 'show', f'{rev}:{f}'], capture_output=True).stdout.decode()
    new = open(f'{wt}/{f}', encoding='utf-8').read()
    same = strip(old) == strip(new)
    do, dn = docs(old), docs(new)
    ch = sum(a != b for a, b in zip(do, dn)) if len(do) == len(dn) else 'count differs'
    w = max(len(l) for l in new.split('\n'))
    print(f'{f}\tcode-identical {same}\tdocstrings {len(do)}->{len(dn)}\tchanged {ch}\tmax-width {w}')
    ok &= same and len(do) == len(dn) and w <= 100
print('RESULT', 'OK' if ok else 'FAIL')
