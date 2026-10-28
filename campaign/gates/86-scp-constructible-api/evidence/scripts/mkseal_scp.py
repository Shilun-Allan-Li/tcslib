"""Seal the moved block of `Constructible` (python3 -I): mkseal_scp.py <Constructible.lean> <out.lean>.
The block (the six private helpers and `spaceConstructible_poly`) is wrapped in one section that
makes the other-file TCSlib definitions it reaches locally irreducible and erases the three
@[simp] TCSlib definitions of the environment; the rest of the file stays outside the seal."""
import sys
src, out = sys.argv[1:3]
s = open(src, encoding='utf-8').read()
SEAL = ['Complexity.transduce', 'Complexity.transducerTM', 'Turing.FinTM.polyUnaryTM',
        'Turing.FinTM.prependTM', 'Turing.FinTM.bufferedCompTM', 'Turing.FinTM.ComputesFunInTime',
        'Turing.FinTM.ComputesInTime', 'Turing.FinTM.ComputesInSpace', 'Turing.MultiTapeTM.spaceUsed',
        'Turing.MultiTapeTM.initCfg', 'Turing.Cfg.init', 'Complexity.logSpace']
SIMPDEFS = ['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg']
start = "/-- The tail transducer's transition: one bit of state, \"the first bit has been read\". -/\n"
stop = "\nend Complexity\n"
assert s.count(start) == 1 and s.endswith(stop) and s.count(stop) == 1
i = s.index(start)
head = ('section SCPSeal\n-- seal: the other-file TCSlib definitions the moved block reaches, '
        'and the @[simp] ones erased\nattribute [-simp] ' + ' '.join(SIMPDEFS) + '\n'
        'attribute [local irreducible]\n' + ''.join('  ' + d + '\n' for d in SEAL) + '\n')
body = s[i:len(s) - len(stop)]
r = s[:i] + head + body + '\nend SCPSeal\n' + stop
open(out, 'w', encoding='utf-8').write(r)
print(f"sealed {len(SEAL)} definitions in 1 region; erased {len(SIMPDEFS)}")
