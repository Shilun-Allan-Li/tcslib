"""Compare two campaign_style_lint outputs by line set (python3 -I).
Usage: lint_compare.py <base.txt> <head.txt>
Lines are compared after collapsing runs of spaces (column padding); FAIL/WARN lines added or
removed are listed; the owned files' FAIL/WARN lines are listed separately.
Exit 0 iff no FAIL or WARN line is added."""
import re, sys
OWNED = ('TCSlib/Cryptography/Hashing/SIS/Columns.lean',
         'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean')
def load(p):
    return [re.sub(r' +', ' ', l.rstrip()) for l in open(p) if l.strip()]
b, h = load(sys.argv[1]), load(sys.argv[2])
for name, lines in (('base', b), ('head', h)):
    print(f'{name}: {lines[-1]}')
sev = lambda l: l.split(' ', 1)[0]
added = sorted(set(h) - set(b)); removed = sorted(set(b) - set(h))
print('# added lines:'); [print('  + ' + l) for l in added if not l.startswith('style_lint:')]
print('# removed lines:'); [print('  - ' + l) for l in removed if not l.startswith('style_lint:')]
for name, lines in (('base', b), ('head', h)):
    own = [l for l in lines if sev(l) in ('FAIL', 'WARN') and any(o in l for o in OWNED)]
    print(f'owned-file FAIL/WARN lines at {name}: {len(own)}'); [print('  ' + l) for l in own]
bad = [l for l in added if sev(l) in ('FAIL', 'WARN')]
print(f'LINT COMPARE: added FAIL={sum(sev(l)=="FAIL" for l in bad)} '
      f'added WARN={sum(sev(l)=="WARN" for l in bad)} -> {"PASS" if not bad else "REVIEW"}')
sys.exit(1 if bad else 0)
