"""Summarize the axioms / dependency-trace probe log (python3 -I).

usage: axioms_report.py PROBE_LOG BASE_SORRIES [--allow-sorry NAME,...]
Joins the wrapped `GSWCORE-AXIOMS` records, prints one line per stored constant of the five
owned modules, then the 29 targets with their axioms and the sorried constants reached.
PASS when every constant uses only propext, Classical.choice, Quot.sound, except constants
explicitly allowed to reach `sorryAx` (checkpoints: through cited later-unit targets only).
"""
import re, sys

log, sorries = sys.argv[1], sys.argv[2]
allow = set()
if '--allow-sorry' in sys.argv:
    allow = set(sys.argv[sys.argv.index('--allow-sorry') + 1].split(','))
text = open(log).read()
recs, cur = [], None
for line in text.splitlines():
    if line.startswith('GSWCORE-AXIOMS'):
        if cur:
            recs.append(cur)
        cur = line
    elif cur is not None and line.startswith(' '):
        cur += line
    else:
        if cur:
            recs.append(cur)
        cur = None
if cur:
    recs.append(cur)
NS = 'TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.'
targets = []
for l in open(sorries):
    m = re.match(r'(TCSlib/\S+/GSW/(\w+)): \d+: (.*)$', l.strip())
    if m:
        targets += [(m[2], NS + n.strip()) for n in m[3].split(',')]
STD = {'propext', 'Classical.choice', 'Quot.sound'}
info, ok = {}, True
summary = [r for r in recs if r.startswith('GSWCORE-AXIOMS-SUMMARY')]
for r in recs:
    m = re.match(r'GSWCORE-AXIOMS (\S+) (\S+) axioms=\[(.*?)\] closure=(\d+) sorried=\[(.*?)\]', r)
    if not m:
        continue
    axs = {a.strip() for a in m[3].split(',') if a.strip()}
    sor = [s.strip() for s in m[5].split(',') if s.strip()]
    info[m[2]] = (m[1], axs, sor, int(m[4]))
for name, (mod, axs, sor, n) in sorted(info.items()):
    bad = axs - STD
    flag = 'OK' if not bad else ('ALLOWED' if bad == {'sorryAx'} and name in allow else 'FAIL')
    ok &= flag != 'FAIL'
    print(f'{flag:7} {mod.rsplit(".", 1)[-1]:9} {name.replace(NS, "")} axioms={sorted(axs)} '
          f'closure={n} sorried={[s.replace(NS, "") for s in sor]}')
print('--- targets ---')
for f, t in [x for x in targets if x[0] in ('Gadget', 'Noise', 'Scheme', 'Symmetric', 'Eval')]:
    if t not in info:
        print(f'MISSING {t}')
        ok = False
        continue
    mod, axs, sor, n = info[t]
    print(f'{f:9} {t.replace(NS, ""):32} {sorted(axs)} sorried={[s.replace(NS, "") for s in sor]}')
print(summary[0] if summary else 'NO SUMMARY')
print(f'constants parsed: {len(info)}')
print('AXIOMS ' + ('PASS' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
