import sys, re
L = open(sys.argv[1]).read().split('\n'); txt = open(sys.argv[2]).read()
errs = sorted(set(int(m.group(1)) for m in re.finditer(r'\.lean:(\d+):\d+: error', txt)))
warns = re.findall(r'\.lean:(\d+):\d+: warning: (.*)', txt)
ctl = [(i+1, l) for i, l in enumerate(L) if l.startswith('/-- Control')]
sec_end = next(i+1 for i, l in enumerate(L) if l == 'end F5Seal')
blocks = []
for n, (ln, l) in enumerate(ctl):
    nxt = ctl[n+1][0] if n + 1 < len(ctl) else sec_end
    end = min(nxt, ln + 6)
    blocks.append((ln, end, l))
used = set()
for ln, end, l in blocks:
    hit = [e for e in errs if ln < e < end]; used |= set(hit)
    print(('FAILS' if hit else 'PASSES'), l[4:].split(':')[0], '|', l.split('`')[1])
other = [e for e in errs if e not in used]
print('errors total', len(errs), '; control errors', len(used), '; errors outside the controls:', other)
for e in other: print('  line', e, ':', L[e-1][:120])
print('warnings:', warns)
