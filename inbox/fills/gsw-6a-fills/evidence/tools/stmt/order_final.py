"""order_final.py <worktree> <order.txt> <new-module>...: inserts each new module right after the last
module it imports (TCSlib imports, read from the worktree), new modules processed in dependency order,
facades after their children; prints the resulting order."""
import sys, re, os
wt, order = sys.argv[1], sys.argv[2]; new = sys.argv[3:]
mods = [l.strip() for l in open(order) if l.strip()]
def imps(m):
    return [x.replace('.', '/') for x in re.findall(r'^import\s+(TCSlib\S*)', open(os.path.join(wt, m + '.lean'), encoding='utf8').read(), re.M)]
pending = list(new)
while pending:
    for m in pending:
        deps = imps(m)
        if all(d in mods for d in deps):
            pos = max((mods.index(d) for d in deps), default=-1)
            mods.insert(pos + 1, m); pending.remove(m); break
    else:
        sys.exit('cycle or missing import: ' + ' '.join(pending))
# a changed facade must come after every child it imports (already true for existing ones)
for m in mods:
    for d in imps(m) if os.path.exists(os.path.join(wt, m + '.lean')) else []:
        assert mods.index(d) < mods.index(m), (m, d)
print('\n'.join(mods))
