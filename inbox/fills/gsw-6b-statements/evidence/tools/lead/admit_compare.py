"""admit_compare.py <base-sorries.txt> <summary.tsv>... [--restrict <modules-file>] [--extra <tsv>]
(gsw-6b-statements, new): compare the `sorry` warnings recorded in pbuild summaries (module, decls=...)
with an expected list. Expected = base-sorries.txt (module: count: names), restricted to the modules of
--restrict if given, plus --extra rows (module<TAB>name). A summary row's names are compared as short
names (the namespace-free tail after the last '.' is NOT taken: names are compared exactly as the
warning's declaration header prints them, and base-sorries' names are matched by suffix). Prints
MATCH/MISSING/EXTRA per module and a total; exit 1 on any difference."""
import sys, collections
args = sys.argv[1:]
restrict = extra = None
if '--restrict' in args:
    i = args.index('--restrict'); restrict = [l.strip() for l in open(args[i+1]) if l.strip()]; del args[i:i+2]
if '--extra' in args:
    i = args.index('--extra'); extra = args[i+1]; del args[i:i+2]
base, sums = args[0], args[1:]
exp = collections.defaultdict(list)
for l in open(base):
    if ':' not in l: continue
    m, c, names = l.rstrip('\n').split(': ', 2)
    exp[m] = [n.strip() for n in names.split(',') if n.strip()]
    assert len(exp[m]) == int(c), m
if restrict is not None:
    rs = set(restrict); exp = collections.defaultdict(list, {m: v for m, v in exp.items() if m in rs})
if extra:
    for l in open(extra):
        if l.strip() and not l.startswith('#'):
            m, n = l.rstrip('\n').split('\t'); exp[m].append(n)
got = collections.defaultdict(list)
for s in sums:
    for l in open(s):
        f = l.rstrip('\n').split('\t')
        if len(f) < 6 or not f[1].startswith('rc='): continue
        names = f[5][len('decls='):]
        got[f[0]] = [n for n in names.split(',') if n]   # last run of a module wins
bad = 0
def short(n): return n.split('.')[-1]
for m in sorted(set(exp) | set(got)):
    e = sorted(exp.get(m, [])); g = sorted(got.get(m, []))
    # names in base-sorries are short or dotted tails; compare by the dotted tail
    ge = sorted(x for x in g); ok = len(e) == len(g) and all(any(x == y or x.endswith('.' + y) or y.endswith('.' + x) for y in e) for x in g)
    if not ok:
        bad += 1; print('DIFF', m, 'expected', e, 'got', g)
tot_e = sum(len(v) for v in exp.values()); tot_g = sum(len(v) for v in got.values())
mods_e = sum(1 for v in exp.values() if v); mods_g = sum(1 for v in got.values() if v)
print(f'expected {tot_e} in {mods_e} modules; got {tot_g} in {mods_g} modules; differing modules {bad}')
sys.exit(1 if bad else 0)
