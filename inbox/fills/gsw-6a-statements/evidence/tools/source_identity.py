"""source_identity.py <repo> <final-rev> <SOURCE-SHA256SUMS> <bootstrap summary.txt>: for every module checked
by the bootstrap sweep, the source SHA-256 recorded at check time must equal the pack's base hash
(SOURCE-SHA256SUMS) and the hash of the file at <final-rev>; so the sweep checked the final head's bytes."""
import sys, subprocess, hashlib
repo, rev, sums, summ = sys.argv[1:5]
base = {}
for l in open(sums):
    h, p = l.rstrip('\n').split(None, 1); base[p.strip().lstrip('*')] = h
bad = n = 0
for l in open(summ):
    f = l.rstrip('\n').split('\t')
    m = f[0]; sha = [x for x in f if x.startswith('sha256=')][0][7:]
    path = m + '.lean'
    fin = hashlib.sha256(subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}'], capture_output=True).stdout).hexdigest()
    ok = sha == base.get(path) == fin
    n += 1; bad += not ok
    if not ok: print(f'DIFF\t{path}\tchecked={sha}\tbase={base.get(path)}\tfinal={fin}')
print(f'RESULT modules={n} identical_to_base_and_final={n - bad} differing={bad}')
