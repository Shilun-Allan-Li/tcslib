r"""insertion_controls.py <base-file> <head-file> <outdir> <AFTER_LINE:BLOCK_FILE>... (bb1-sim-statements, lead).
Mutation controls of insertion_check.py (run by path, from this directory): on copies of the head,
(C1) one character changed in a base line: FAIL with exactly one difference (a replace of one line);
(C2) one base line deleted: FAIL with exactly one difference (a delete of one line);
(C3) one extra line added elsewhere: FAIL; (C4) the first block moved (cut, and pasted after the
block's anchor line + 3 base lines): FAIL; (C0) the head unchanged: PASS. Prints each result and
ALL_OK."""
import sys, os, subprocess, re
base, head, outd, *specs = sys.argv[1:]
os.makedirs(outd, exist_ok=True)
chk = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'insertion_check.py')
H = open(head, encoding='utf-8').read().split('\n')
blocks = []
for s in specs:
    n, f = s.split(':', 1); blocks.append((int(n), open(f, encoding='utf-8').read()[:-1].split('\n')))
blocks.sort()
inserted = set(); shift = 0
for n, bl in blocks:
    inserted |= set(range(n + shift, n + shift + len(bl))); shift += len(bl)
base_idx = [i for i in range(len(H)) if i not in inserted and H[i].strip()]
def run(name, lines):
    p = os.path.join(outd, f'{name}.lean')
    open(p, 'w', encoding='utf-8').write('\n'.join(lines))
    r = subprocess.run([sys.executable, '-I', chk, base, p, *specs], capture_output=True, text=True)
    open(os.path.join(outd, f'{name}.out'), 'w').write(r.stdout)
    os.remove(p)
    res = r.stdout.strip().split('\n')[-1]
    nd = int(re.search(r'^differences: (\d+)', r.stdout, re.M).group(1))
    kinds = re.search(r'^differences: \d+ \((.*)\)', r.stdout, re.M).group(1)
    return res, nd, kinds
ok = True
def want(name, got, res, nd=None, kinds=None):
    global ok
    good = got[0] == res and (nd is None or got[1] == nd) and (kinds is None or got[2] == kinds)
    ok &= good
    print(f"{name}: {got[0]}, differences {got[1]} ({got[2]}) -> {'as expected' if good else 'UNEXPECTED'}")
want('C0 unchanged', run('C0', H), 'PASS', 0)
i = base_idx[len(base_idx) // 3]; L = H[:]; L[i] = L[i][:-1] + ('x' if L[i][-1] != 'x' else 'y')
want(f'C1 one character changed (head line {i + 1})', run('C1', L), 'FAIL', 1, 'replace')
i = base_idx[len(base_idx) // 2]; L = H[:i] + H[i + 1:]
want(f'C2 one base line deleted (head line {i + 1})', run('C2', L), 'FAIL', 1, 'delete')
i = base_idx[2 * len(base_idx) // 3]; L = H[:i] + ['-- an extra line'] + H[i:]
want(f'C3 one extra line (before head line {i + 1})', run('C3', L), 'FAIL')
n, bl = blocks[0]; s0 = n
L = H[:s0] + H[s0 + len(bl):]; L = L[:n + 3] + bl + L[n + 3:]
want(f'C4 first block moved (3 base lines down)', run('C4', L), 'FAIL')
print('ALL_OK', ok)
sys.exit(0 if ok else 1)
