#!/usr/bin/env python3
"""UNRUN: compare full frozen public kernel types globally, independently of file moves."""
import argparse
import hashlib
import json
from pathlib import Path
import runpy


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--inventory', required=True)
    ap.add_argument('--frozen', required=True)
    ap.add_argument('--current', required=True)
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    iv = runpy.run_path(str(Path(__file__).with_name('checkpoint_inventory.py')))
    inv = iv['load'](args.inventory)
    baseline = Path(inv['root']) / 'evidence/axioms/m0-sp-w3/StmtDump.jsonl'
    iv['need'](Path(args.frozen).read_bytes() == baseline.read_bytes(),
               'Frozen census must equal the complete canonical M0 full-type dump')
    maps = []
    for path in [args.frozen, args.current]:
        rows = [json.loads(line) for line in Path(path).read_text().splitlines()]
        names = [row['name'] for row in rows]
        iv['need'](len(names) == len(set(names)) and names, 'Duplicate/empty kernel-type census')
        maps.append({row['name']: row for row in rows})
    old, now = maps
    removed = sorted(set(old) - set(now))
    changed = [name for name in old if name in now and
               (old[name]['kind'], old[name]['type']) != (now[name]['kind'], now[name]['type'])]
    iv['need'](not removed and not changed, 'Frozen full kernel types removed/changed globally')
    output = Path(args.output)
    iv['need'](not output.exists(), 'Preserve old type comparison; choose fresh output')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(dict(head=inv['head'], inventory_sha256=inv['inventory_sha256'],
        frozen_types=len(old), current_types=len(now), removed=removed, changed=changed,
        additional_current_types=sorted(set(now)-set(old)),
        input_sha256={str(Path(path).resolve()): hashlib.sha256(Path(path).read_bytes()).hexdigest()
                      for path in [args.frozen,args.current]}, all_frozen_types_preserved=True,
        qualification='Full kernel-expression types, including generated public fields/constructors, '
                      'supplement source headers/prose. New proof/helper admission is separate.'),indent=2)+'\n')
    print('FROZEN_KERNEL_TYPES_PASS', len(old), 'preserved')


if __name__ == '__main__':
    main()
