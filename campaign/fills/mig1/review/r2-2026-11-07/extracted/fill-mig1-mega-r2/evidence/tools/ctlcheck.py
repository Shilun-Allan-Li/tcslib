"""ctlcheck.py <controls.lean> <lean output> <expect: pass|fail>
Multiplicity checker for paired seal controls (gate 16 R2-2): every `example` block must get exactly
one `error` diagnostic in the sealed run (expect=fail) or none in the unsealed run (expect=pass); no
error may fall outside an example; the recorded exit code must be nonzero for fail, zero for pass."""
import re, sys
src, out, expect = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(src, encoding='utf-8').read().split('\n')
starts = [i + 1 for i, l in enumerate(lines) if l.startswith('example')]
ends = starts[1:] + [len(lines) + 1]
def block(ln):
    for s, e in zip(starts, ends):
        if s <= ln < e: return s
    return None
o = open(out, encoding='utf-8').read()
errs = [int(m.group(1)) for m in re.finditer(r'^[^\n]*?:(\d+):\d+: error', o, re.M)]
m = re.search(r'^exit=(\d+)', o, re.M); code = int(m.group(1)) if m else None
count = {s: 0 for s in starts}; stray = []
for ln in errs:
    b = block(ln)
    if b is None: stray.append(ln)
    else: count[b] += 1
want = 1 if expect == 'fail' else 0
bad = [(s, c) for s, c in count.items() if c != want]
ok_exit = (code is not None) and ((code != 0) if expect == 'fail' else (code == 0))
print(f'examples={len(starts)} errors={len(errs)} stray={stray} exit={code} expected_per_example={want}')
for s, c in bad: print(f'  example at line {s}: {c} error(s), expected {want}')
print('RESULT:', 'PASS' if not bad and not stray and ok_exit else 'FAIL')
