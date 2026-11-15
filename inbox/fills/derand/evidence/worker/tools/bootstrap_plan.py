"""Select an upstream closure in the issued topological order; never reorder modules."""
from pathlib import Path
import sys

order_path, destination, *roots = sys.argv[1:]
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    for line in Path(module + '.lean').read_text().splitlines():
        if line.startswith('import '):
            for name in line.split()[1:]:
                if name.startswith('TCSlib.'):
                    visit(name.replace('.', '/'))
for module in roots:
    visit(module)
order = Path(order_path).read_text().splitlines()
missing = seen - set(order)
if missing:
    raise SystemExit('Missing prerequisites from issued order: ' + ', '.join(sorted(missing)))
selected = [module for module in order if module in seen]
Path(destination).write_text('\n'.join(selected) + '\n')
print(f'Upstream closure: {len(selected)} of {len(order)} issued modules -> {destination}')
