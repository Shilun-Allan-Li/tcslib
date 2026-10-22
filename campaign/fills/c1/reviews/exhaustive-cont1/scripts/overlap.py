"""Open PRs' replay closures (downstream of their changed modules, in the patched tip tree) vs this
landing's. usage: python3 -I overlap.py <repo> <patched tip worktree> <tip sha> <closure.py> <pr:branch>..."""
import subprocess, sys
repo, wt, tip, closure = sys.argv[1:5]
g = lambda *a: subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True).stdout.strip()
down = lambda ms: set(subprocess.run(['python3', '-I', closure, wt, 'down'] + ms, capture_output=True, text=True).stdout.split())
mine = down(['TCSlib/Complexity/ClassNP/ExhaustiveReplay'])
print('this landing\'s replay closure at the tip (%d): %s' % (len(mine), ' '.join(sorted(mine))))
for spec in sys.argv[5:]:
    pr, br = spec.split(':', 1)
    head = g('rev-parse', br); mb = g('merge-base', br, tip)
    files = [f for f in g('diff', '--name-only', mb, br, '--', 'TCSlib').split('\n') if f.endswith('.lean')]
    ms = [f[:-5] for f in files]
    cl = down(ms)
    print(f"{pr} {br} {head[:8]} (merge base with the tip {mb[:8]}{'= tip' if mb == tip else ''}): changed {ms}; closure {len(cl)} modules; overlap with this landing: {sorted(cl & mine)}")
