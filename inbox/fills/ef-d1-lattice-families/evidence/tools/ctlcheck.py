"""ctlcheck.py <ctl.lean> <ctl.out> <sealed 0|1>: every NEG line fails exactly once when sealed and
passes unsealed; every POS passes; no stray error."""
import re, sys
src = open(sys.argv[1], encoding='utf-8').read().split('\n'); out = open(sys.argv[2], encoding='utf-8').read()
sealed = sys.argv[3] == '1'
errs = [int(m.group(1)) for m in re.finditer(r'^\S+\.lean:(\d+):\d+: error[:(]', out, re.M)]
neg = [i + 1 for i, l in enumerate(src) if l.rstrip().endswith('--NEG')]
pos = [i + 1 for i, l in enumerate(src) if l.rstrip().endswith('--POS')]
ok = True
for n in neg:
    c = errs.count(n)
    want = 1 if sealed else 0
    if c != want: ok = False; print('NEG line', n, 'errors', c, 'want', want)
stray = [e for e in errs if e not in neg]
if stray: ok = False; print('stray errors at', stray)
print(f"{sys.argv[1].split('/')[-1]}: NEG={len(neg)} POS={len(pos)} errors={len(errs)} sealed={sealed} ALL_OK={ok}")
