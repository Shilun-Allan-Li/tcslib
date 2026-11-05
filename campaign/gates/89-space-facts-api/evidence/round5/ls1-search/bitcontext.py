"""Context for the binary-length sweep: each declaration's hits with three lines before and two after.
Usage: python3 -I bitcontext.py <repo worktree> <bitsweep.tsv> <out>"""
import subprocess, sys, collections
wt, tsv, out = sys.argv[1:4]
lines = open(tsv).read().split('\n')
rev = lines[0].split()[2].rstrip(';')
groups = collections.OrderedDict()
for l in lines[1:]:
    if not l.strip(): continue
    loc, decl, _ = l.split('\t', 2)
    f, n = loc.rsplit(':', 1)
    groups.setdefault((f, decl), []).append(int(n))
res = [f'# rev {rev}; {len(groups)} declarations']
for (f, d), ns in groups.items():
    src = subprocess.run(['git', '-C', wt, 'show', f'{rev}:{f}'], capture_output=True, text=True, check=True).stdout.split('\n')
    a, b = max(1, min(ns) - 3), min(len(src), max(ns) + 2)
    res.append(f'### {f} · {d} · lines {ns}')
    res += [f'{k:5d} {src[k - 1]}' for k in range(a, b + 1)]
open(out, 'w').write('\n'.join(res) + '\n'); print(len(groups), 'declarations')
