"""Insert only new helpers, keeping every issued module in its issued order."""
from pathlib import Path

issued = Path('evidence/inputs/issued/outbox/fills/derand-r2/order.txt').read_text().splitlines()
old = set(issued)
done, result, active = set(), [], set()

def dependencies(module):
    for line in Path(module + '.lean').read_text().splitlines():
        if line.startswith('import '):
            for name in line.split()[1:]:
                if name.startswith('TCSlib.'):
                    yield name.replace('.', '/')

def helper(module):
    if module in done:
        return
    assert module not in old, ('issued prerequisite appears too late', module)
    assert module not in active, ('cycle', module)
    assert module.startswith(('TCSlib/Complexity/Randomized/SeedMajority/',
                              'TCSlib/Cryptography/Randomness/Derandomization/')), module
    active.add(module)
    for dependency in dependencies(module):
        helper(dependency)
    active.remove(module)
    done.add(module)
    result.append(module)

for module in issued:
    for dependency in dependencies(module):
        helper(dependency)
    assert module not in done
    done.add(module)
    result.append(module)
assert [module for module in result if module in old] == issued
assert len(result) == 387 and len(done) == len(result)
destination = Path('evidence/logs/final-order.txt')
destination.write_text('\n'.join(result) + '\n')
print(f'FINAL ORDER PASS: {len(issued)} issued modules unchanged in order; '
      f'{len(result) - len(issued)} helpers inserted; no cycle or late prerequisite')
