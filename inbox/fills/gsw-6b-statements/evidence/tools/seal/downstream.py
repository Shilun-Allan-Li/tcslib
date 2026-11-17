"""downstream.py <worktree> <order.txt> <changed module>...: modules of <order.txt> whose TCSlib import
closure (read from the worktree's sources) contains a changed module; prints count and list."""
import sys, re, os
wt, order = sys.argv[1], sys.argv[2]
changed = set(sys.argv[3:])
mods = [l.strip() for l in open(order) if l.strip()]
imps = {}
def imports(m):
    if m in imps: return imps[m]
    p = os.path.join(wt, m + '.lean')
    r = []
    if os.path.exists(p):
        for l in open(p, encoding='utf8'):
            mm = re.match(r'^import\s+(TCSlib\S*)', l)
            if mm: r.append(mm.group(1).replace('.', '/'))
    imps[m] = r; return r
memo = {}
def down(m):
    if m in memo: return memo[m]
    memo[m] = False
    res = m in changed or any(down(i) for i in imports(m))
    memo[m] = res; return res
ds = [m for m in mods if down(m)]
print(len(ds), 'of', len(mods))
for m in ds: print(m)
