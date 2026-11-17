r"""(bb1-sim, lead: ADAPTED from bb1-sim-statements' admissions.py: a fourth argument <expected-removals> (same format)
is subtracted from the expectation; nothing else changed.)
admissions.py <worktree> <base-sorries.txt> <expected-additions> <expected-removals> <results.jsonl>... (bb1-sim-statements, lead).
The admissions at a head: every `declaration uses 'sorry'` warning in the module logs (the later
results.jsonl overrides an earlier one module by module: the bootstrap at the base, then the series
sweep), attributed to the declaration whose name starts at the warning's line and column in the
source at the worktree (the checked head). Compared with base-sorries.txt plus <expected-additions>
(`Module: name, name` lines; `-` for none). Prints the table, the differences and PASS/FAIL."""
import sys, json, os, re
wt, basef, addf, remf, *runs = sys.argv[1:]
logs = {}
for rj in runs:
    d = os.path.dirname(rj)
    for l in open(rj):
        r = json.loads(l)
        if 'module' in r:
            logs[r['module']] = os.path.join(d, 'mods', r['module'].replace('/', '_') + '.log')
def parse(path):
    exp = {}
    for l in open(path, encoding='utf-8'):
        l = l.strip()
        if not l or l.startswith('TOTAL') or l == '-' or l.startswith('#'): continue
        m, rest = l.split(':', 1)
        names = rest.split(':', 1)[1] if re.match(r'\s*\d+:', rest) else rest
        exp.setdefault(m.strip(), set()).update(n.strip() for n in names.split(',') if n.strip())
    return exp
exp = parse(basef)
for m, ns in parse(addf).items(): exp.setdefault(m, set()).update(ns)
for m, ns in parse(remf).items():
    exp[m] = exp.get(m, set()) - ns
    if not exp[m]: del exp[m]
got = {}
pat = re.compile(r"^(\S+\.lean):(\d+):(\d+): warning: declaration uses 'sorry'", re.M)
for m, lp in sorted(logs.items()):
    for f, ln, col in pat.findall(open(lp, encoding='utf-8', errors='replace').read()):
        src = open(os.path.join(wt, f), encoding='utf-8').read().split('\n')[int(ln) - 1]
        name = re.match(r'[^\s(:{\[]+', src[int(col):]).group(0)
        got.setdefault(f[:-5], set()).add(name)
ok = got == exp
for m in sorted(set(got) | set(exp)):
    g, e = got.get(m, set()), exp.get(m, set())
    print(f"{'OK  ' if g == e else 'DIFF'} {m}: {len(g)}: {', '.join(sorted(g))}" +
          ('' if g == e else f"  (expected {', '.join(sorted(e))})"))
print(f'modules checked {len(logs)}; admissions {sum(map(len, got.values()))} declarations in {len(got)} modules; '
      f'expected {sum(map(len, exp.values()))} in {len(exp)}')
print('PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
