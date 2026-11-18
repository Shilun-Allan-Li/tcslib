"""axcheck6b.py <probe.log> <out>: (6b prereqs re-replay on #8) reads the Axioms probe log: each `AX\t<name>\t[...]`
entry (possibly wrapped over lines) gives OK when its axioms are within {propext, Classical.choice, Quot.sound};
counts sorryAx anywhere and `error` diagnostic lines (`MISSING` / `: error`)."""
import sys, re
log, out = sys.argv[1:3]; t = open(log, encoding='utf-8').read()
STD = {'propext', 'Classical.choice', 'Quot.sound'}; L = []; bad = 0
for m in re.finditer(r'^AX\t(\S+)\t\[([^\]]*)\]', t, re.M | re.S):
    ax = sorted(x.strip() for x in m.group(2).split(',') if x.strip()); ok = set(ax) <= STD; bad += not ok
    L.append(f'{"OK" if ok else "BAD"}\t{m.group(1)}\t{ax}')
err = len(re.findall(r'(: error|MISSING)', t))
L.append(f'checked {len(L)}; bad {bad}; sorryAx {"sorryAx" in t}; error lines {err}')
open(out, 'w').write('\n'.join(L) + '\n'); print('\n'.join(L))
