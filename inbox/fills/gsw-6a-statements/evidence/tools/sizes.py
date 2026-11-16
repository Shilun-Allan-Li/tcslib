"""sizes.py <repo> <rev> <file>...: check 10, lines and maximum width (Python len, characters) of each file
at <rev>, with every line over 100 characters listed."""
import sys, subprocess
repo, rev = sys.argv[1:3]
for f in sys.argv[3:]:
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True)
    if r.returncode: print(f'{f}\tABSENT'); continue
    lines = r.stdout.decode('utf8').split('\n')
    if lines and lines[-1] == '': lines.pop()
    w = max((len(l) for l in lines), default=0)
    over = [i + 1 for i, l in enumerate(lines) if len(l) > 100]
    print(f'{f}\tlines={len(lines)}\tmax_width={w}\tover100={over}')
