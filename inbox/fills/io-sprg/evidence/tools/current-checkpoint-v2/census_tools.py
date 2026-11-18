#!/usr/bin/env python3
"""UNRUN candidate: prepare exact-owner graph/print probes; never invokes Lean.

Root runs the resulting probes separately under the existing serial slot runner.
Outputs must be fresh probe paths outside implementation sources.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action', choices=['graph', 'prints'])
    ap.add_argument('--inventory', required=True)
    ap.add_argument('--template', default='evidence/probes/io_sprg_m0/CensusGraph.lean')
    ap.add_argument('--census')
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    iv = runpy.run_path(str(Path(__file__).with_name('checkpoint_inventory.py')))
    inv = iv['load'](args.inventory)
    root, output = Path(inv['root']), Path(args.output).resolve()
    iv['need'](output.is_relative_to(root / 'evidence/probes') and output.suffix == '.lean',
               'Probe output must be a Lean file under evidence/probes')
    iv['need'](not output.exists(), 'Choose a fresh probe path, preserving historical M0 probes')
    imports = ['import Lean', *('import ' + module for module in inv['owners'])]
    binding = dict(head=inv['head'], inventory_sha256=inv['inventory_sha256'], owners=inv['owners'])
    if args.action == 'graph':
        template = Path(args.template)
        if not template.is_absolute():
            template = root / template
        source = template.read_text()
        start = source.index('def owners : List Name := [')
        end = source.index(']', start)
        source = source[:start] + 'def owners : List Name := [\n  ' + ',\n  '.join(
            '`' + name for name in inv['owners']) + source[end:]
        source = re.sub(r'^import (?:Lean|TCSlib\S*)\n', '', source, flags=re.M)
        source = '\n'.join(imports) + '\n' + source
        binding['template_sha256'] = hashlib.sha256(template.read_bytes()).hexdigest()
        binding['qualification'] = 'Original graph traversal/body retained; imports and owner array replaced only.'
    else:
        iv['need'](args.census is not None, 'prints requires the current complete stored census')
        census_path = Path(args.census)
        census = json.loads(census_path.read_text())
        iv['need'](all(row['module'] in inv['owners'] for row in census), 'Census root outside owners')
        names = [row['name'] for row in census if row['kind'] == 'theorem'
                 and not row['private'] and not row['internal']]
        iv['need'](names and len(names) == len(set(names)), 'Empty/duplicate public theorem census')
        source = '\n'.join(imports) + '\n\n' + ''.join('#print axioms ' + n + '\n' for n in sorted(names))
        binding.update(public_theorems=sorted(names), census_sha256=hashlib.sha256(census_path.read_bytes()).hexdigest())
    binding['probe_module'] = output.relative_to(root).as_posix()[:-5]
    binding['probe_sha256'] = hashlib.sha256(source.encode()).hexdigest()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as handle:
        handle.write(source)
    with output.with_suffix('.binding.json').open('x') as handle:
        handle.write(json.dumps(binding, indent=2) + '\n')
    print('PREPARED_ONLY', args.action, str(output), len(inv['owners']), 'owners; Lean not invoked')


if __name__ == '__main__':
    main()
