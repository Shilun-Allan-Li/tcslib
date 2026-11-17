r"""tipcensus.py <repo> <rev> <out> <name=records.jsonl>...: per-module `declaration uses 'sorry'` counts at <rev> taken from
build records whose source SHA-256 equals the module's source at <rev> (any record set; a module's sorry warnings depend only on
its own source). Every TCSlib/audits module at <rev> is listed with its count and the record sets that match; modules with no
matching rc-0 record, and modules whose matching records disagree, are reported. Prints the tree-wide total."""
import sys, json, hashlib, subprocess
repo, rev, out = sys.argv[1:4]
git = lambda *a: subprocess.run(['git', '-C', repo, *a], capture_output=True, check=True).stdout
files = [f[:-5] for f in git('ls-tree', '-r', '--name-only', rev, 'TCSlib', 'TCSlib.lean', 'audits').decode().split() if f.endswith('.lean')]
recs = {}
for a in sys.argv[4:]:
    n, f = a.split('=', 1)
    for l in open(f):
        r = json.loads(l)
        if 'module' in r and r['rc'] == 0: recs.setdefault((r['module'], r['source_sha256']), {}).setdefault(r['sorry'], set()).add(n)
tot = 0; norec = []; disagree = []
with open(out, 'w') as o:
    for m in sorted(files):
        h = hashlib.sha256(git('show', f'{rev}:{m}.lean')).hexdigest(); d = recs.get((m, h))
        if not d: norec.append(m); o.write(f'NOREC {m}\n'); continue
        if len(d) > 1: disagree.append(m)
        c = min(d); tot += c
        o.write(f'{c:3d} {m}  [{",".join(sorted(set().union(*d.values())))}]\n')
    o.write(f'TOTAL {tot} sorry warnings over {len(files) - len(norec)} modules with a matching record; no record {len(norec)} {norec}; disagreeing {disagree}\n')
print(open(out).read().splitlines()[-1])
