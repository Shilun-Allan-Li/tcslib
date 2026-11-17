"""admissions.py <base-sorries.txt> <targets.tsv> <summary>...: check 4. Per module, the number of
"declaration uses 'sorry'" warnings in the build summaries (the last record of each module wins) is
compared with base-sorries.txt (existing modules) and with the number of admitted targets (new modules,
from targets.tsv: `module<TAB>count`). Prints every module with a nonzero count or an expectation, and
totals; exit 1 on any mismatch or on a module of the expectations that was not built."""
import sys, re
base = {}
for l in open(sys.argv[1]):
    m = re.match(r'^(\S+): (\d+): ', l)
    if m: base[m.group(1)] = int(m.group(2))
new = {}
for l in open(sys.argv[2]):
    if l.strip() and not l.startswith('#'):
        a, b = l.split('\t'); new[a] = int(b)
built = {}
for s in sys.argv[3:]:
    for l in open(s):
        f = l.rstrip('\n').split('\t')
        if len(f) > 3 and f[1].startswith('rc='):
            built[f[0]] = (int(f[1][3:]), int(f[3].split('=')[1]))
bad = 0; tb = tn = 0
for m in sorted(set(base) | set(new) | {k for k, v in built.items() if v[1]}):
    want = base.get(m, new.get(m, 0)); got = built.get(m)
    if got is None: print(f'NOT-BUILT\t{m}\twant={want}'); bad += 1; continue
    ok = got[1] == want and got[0] == 0
    kind = 'base' if m in base else ('new' if m in new else 'other')
    print(f'{"OK" if ok else "MISMATCH"}\t{kind}\t{m}\twarnings={got[1]}\texpected={want}')
    bad += not ok
    if m in base: tb += got[1]
    if m in new: tn += got[1]
print(f'RESULT modules_built={len(built)} base_admissions={tb} (expected {sum(base.values())} in {len(base)} modules) new_admissions={tn} (expected {sum(new.values())} in {len(new)} modules) mismatches={bad}')
sys.exit(1 if bad else 0)
