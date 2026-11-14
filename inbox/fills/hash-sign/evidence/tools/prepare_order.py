import pathlib
import re

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
supplied = (ev / 'inputs/order.txt').read_text().splitlines()
seen, order, roots = set(), [], set()

def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = repo / (module + '.lean')
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            for dep in line.removeprefix('import ').split():
                if dep.startswith('TCSlib.'):
                    visit(dep.replace('.', '/'))
                elif dep.startswith('Mathlib.'):
                    roots.add(dep)
    order.append(module)

# T1/T2 are published interfaces but not in the original admitted target's
# import closure. Add their prerequisites before the owned module.
for module in supplied:
    if module.endswith('/HashAndSign'):
        visit('TCSlib/Cryptography/Games/Forwarding')
    visit(module)
(ev / 'logs/extended-order.txt').write_text('\n'.join(order) + '\n')
(ev / 'logs/mathlib-roots.txt').write_text('\n'.join(sorted(roots)) + '\n')
added = [m for m in order if m not in supplied]
print('supplied modules:', len(supplied), 'extended:', len(order), 'roots:', len(roots))
print('added modules:\n' + '\n'.join(added))
issued_roots = set((ev / 'inputs/roots.txt').read_text().splitlines())
print('additional Mathlib roots:', sorted(roots - issued_roots))
