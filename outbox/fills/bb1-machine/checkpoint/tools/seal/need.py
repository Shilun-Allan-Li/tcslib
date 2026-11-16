"""need.py <worktree> <olean-tree> <tree-rev> <root>...: import closure (topological order, worktree
files) of the roots; prints `<flags> <module>` for every closure module that must be (re)built:
M = olean missing, C = source changed since <tree-rev> (committed or not), D = downstream of those.
`--all` also lists the untouched closure modules with flag `--`."""
import sys, os, re, subprocess
args = sys.argv[1:]; allf = '--all' in args; args = [a for a in args if a != '--all']
wt, tree, rev, *roots = args
def src(m):
    p = os.path.join(wt, m.replace('.', '/') + '.lean')
    return open(p, encoding='utf-8').read() if os.path.exists(p) else None
seen, order, imps = set(), [], {}
def visit(m):
    if m in seen: return
    seen.add(m); s = src(m)
    if s is None: print('NOSRC', m, file=sys.stderr); sys.exit(2)
    imps[m] = [i for i in re.findall(r'^import\s+(\S+)', s, re.M) if i.split('.')[0] == 'TCSlib']
    for i in imps[m]: visit(i)
    order.append(m)
for r in roots: visit(r)
out = subprocess.run(['git','-C',wt,'diff','--name-only',rev,'--','TCSlib','TCSlib.lean'],
   capture_output=True,text=True).stdout.split()
out += [l[3:] for l in subprocess.run(['git','-C',wt,'status','--porcelain','--untracked-files=all'],
   capture_output=True,text=True).stdout.splitlines()]
changed = set(out)
need = {}
for m in order:
    f = ''
    if not os.path.exists(os.path.join(tree, m.replace('.','/')+'.olean')): f += 'M'
    if m.replace('.','/')+'.lean' in changed: f += 'C'
    if any(i in need for i in imps[m]): f += 'D'
    if f: need[m] = f
    if f or allf: print((f or '--').ljust(3), m)
print('# closure', len(order), 'need', len(need), file=sys.stderr)
