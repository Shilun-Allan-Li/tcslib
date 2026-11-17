"""root_binding.py <repo> <rev> <order-file> <summary.tsv>... (gsw-6b-statements, new): the root
build's binding to <rev>. For every module of the order: its last successful build row in the given
pbuild summaries (chronological; last wins) and whether that row's source SHA-256 (at start and end)
equals `git show <rev>:<module>.lean`. Prints module, summary file, rc, errors, sorry count and names,
start, end, source SHA-256, and BOUND/UNBOUND; then totals and the sum of sorry warnings."""
import sys, subprocess, hashlib
repo, rev, order, sums = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
mods = [l.strip() for l in open(order) if l.strip()]
last = {}
for s in sums:
    for l in open(s):
        f = l.rstrip('\n').split('\t')
        if len(f) >= 12 and f[1] == 'rc=0' and f[2] == 'errors=0' and f[3] == 'error_lines=0': last[f[0]] = (s, f)
bad = tot = 0
p = subprocess.Popen(['git', '-C', repo, 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
print('module\tsummary\trc\terrors\tsorry\tdecls\tstart\tend\tsource_sha256\tbinding')
for m in mods:
    p.stdin.write(f'{rev}:{m}.lean\n'.encode()); p.stdin.flush()
    hdr = p.stdout.readline().split(); n = int(hdr[2]); data = p.stdout.read(n); p.stdout.read(1)
    h = hashlib.sha256(data).hexdigest()
    if m not in last: print(f'{m}\t-\t-\t-\t-\t-\t-\t-\t{h}\tUNBUILT'); bad += 1; continue
    s, f = last[m]; ok = f[10] == h and f[11] == h
    bad += not ok; tot += int(f[4].split('=')[1])
    print(f'{m}\t{s.split("/build/")[1]}\t{f[1]}\t{f[2]}\t{f[4]}\t{f[5]}\t{f[6]}\t{f[7]}\t{h}\t{"BOUND" if ok else "UNBOUND"}')
print(f'# {len(mods)} modules; {len(mods) - bad} bound to {rev}; {bad} not; sorry warnings {tot}')
