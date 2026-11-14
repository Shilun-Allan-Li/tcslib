"""Record source-only public/private provider searches for the final review ledger."""
from pathlib import Path
import subprocess

root = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
out = Path(__file__).with_name('provider-searches.log')
assert not out.exists()
commands = [
    ['rg', '-n', 'theorem (takeLen_poly|dropLen_poly)|lemma (takeLen_poly|dropLen_poly)', 'TCSlib'],
    ['rg', '-n', 'tmsat_pt_take', 'TCSlib/Complexity/ClassNP/TMSAT.lean'],
    ['rg', '-n', 'clA5Drop_native', 'TCSlib/Complexity/CookLevin/Hardness.lean'],
    ['rg', '-n', 'private theorem dlb_(take|drop)_poly', 'TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean'],
    ['rg', '-n', 'ReductionSupport',
     '/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence/inputs/order.txt',
     '/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence/inputs/final-r1-order.txt'],
    ['rg', '-n', 'ofFn_blocks_two_symm', 'TCSlib/Cryptography/Asymptotic/OneWay.lean'],
]
with out.open('w') as log:
    for command in commands:
        log.write('$ ' + ' '.join(command) + '\n')
        log.flush()
        p = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        log.write(f'EXIT {p.returncode}\n\n')
print(out)
