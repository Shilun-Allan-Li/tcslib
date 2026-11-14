"""Insert owned helpers and their prerequisites into the issued 150-module sweep.

Run with python3 -I after the final sources are stable. No compiler is invoked.
The issued order must remain an exact subsequence of the resulting order.
"""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--phase', required=True)
args = parser.parse_args()
root, evidence = Path(args.root), Path(args.evidence)
issued = (evidence / 'inputs/order.txt').read_text().splitlines()
prefix = 'TCSlib/Cryptography/Authentication/Signatures/Lamport'
helpers = sorted(p.with_suffix('').relative_to(root).as_posix()
                 for p in (root / prefix).glob('*.lean'))
seen, active, order, sources, roots = set(), set(), [], {}, set()


def visit(module):
    if module in seen:
        return
    assert module not in active, 'import cycle: ' + module
    active.add(module)
    raw = (root / (module + '.lean')).read_bytes()
    sources[module] = hashlib.sha256(raw).hexdigest()
    dependencies = []
    for line in raw.decode().splitlines():
        if line.startswith('import '):
            for dependency in line.split()[1:]:
                if dependency.startswith('TCSlib.'):
                    dependencies.append(dependency.replace('.', '/'))
                elif dependency.startswith('Mathlib.'):
                    roots.add(dependency)
    # The owned module must compile against every delivered helper before the
    # downstream issued sweep proceeds, even if a helper has no direct consumer.
    if module == prefix:
        dependencies.extend(helpers)
    for dependency in dependencies:
        visit(dependency)
    active.remove(module)
    seen.add(module)
    order.append(module)


for module in issued:
    visit(module)
assert [m for m in order if m in set(issued)] == issued, 'issued order was reordered'
assert set(helpers) <= set(order)
issued_roots = set((evidence / 'inputs/roots.txt').read_text().splitlines())
assert roots <= issued_roots, sorted(roots - issued_roots)
directory = evidence / 'inputs'
order_path = directory / (args.phase + '-order.txt')
audit_path = directory / (args.phase + '-order-audit.json')
assert not order_path.exists() and not audit_path.exists()
order_path.write_text('\n'.join(order) + '\n')
audit_path.write_text(json.dumps(dict(issued_count=len(issued), total=len(order),
    helper_count=len(helpers), exact_issued_subsequence=True,
    additions=[m for m in order if m not in set(issued)],
    mathlib_roots=sorted(roots), new_mathlib_roots=[],
    source_sha256=sources, compiler_run=False), indent=2) + '\n')
print(json.dumps(dict(order=str(order_path), issued_count=len(issued),
                     total=len(order), helper_count=len(helpers)), indent=2))
