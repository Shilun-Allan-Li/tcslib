"""[gsw-6b-statements copy of gsw-6a-statements evidence/tools/order_final.py; change: instead of
asserting that every module follows its imports, a module that precedes one of its imports (here
the changed facade GSW, which now imports the new children) is moved right after its last import,
repeated until stable; the final check is kept.]
order_final.py <worktree> <order.txt> <new-module>...: inserts each new module right after the last
module it imports (TCSlib imports, read from the worktree), new modules processed in dependency order,
facades after their children; prints the resulting order."""
import sys, re, os
wt, order = sys.argv[1], sys.argv[2]; new = sys.argv[3:]
mods = [l.strip() for l in open(order) if l.strip()]
def imps(m):
    p = os.path.join(wt, m + '.lean')
    if not os.path.exists(p): return []
    return [x.replace('.', '/') for x in re.findall(r'^import\s+(TCSlib\S*)', open(p, encoding='utf8').read(), re.M)]
pending = list(new)
while pending:
    for m in pending:
        deps = imps(m)
        if all(d in mods for d in deps):
            pos = max((mods.index(d) for d in deps), default=-1)
            mods.insert(pos + 1, m); pending.remove(m); break
    else:
        sys.exit('cycle or missing import: ' + ' '.join(pending))
moved = True
while moved:
    moved = False
    for m in list(mods):
        deps = [d for d in imps(m) if d in mods]
        if deps and max(mods.index(d) for d in deps) > mods.index(m):
            mods.remove(m); pos = max(mods.index(d) for d in deps); mods.insert(pos + 1, m)
            print(f'# moved {m}', file=sys.stderr); moved = True
for m in mods:
    for d in imps(m):
        assert d not in mods or mods.index(d) < mods.index(m), (m, d)
print('\n'.join(mods))
