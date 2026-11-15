"""Diagnostic only: isolate the two bundled-constructor carrier reductions.

These probes are deliberately weaker than the canonical seals. Their results
are never reported as Rule 10 clearance. Every other full-closure mask remains.
"""
import importlib.util
import json
from pathlib import Path

spec = importlib.util.spec_from_file_location('derand_seals', 'evidence/tools/make_seals.py')
seals = importlib.util.module_from_spec(spec)
spec.loader.exec_module(seals)
old = 'let eligible := (status != .reducible || matcher) &&'
new = '''let eligible := name != `Turing.ModuleHost.hostTM &&
      name != `Complexity.IterateFind.copyTM && (status != .reducible || matcher) &&'''
assert old in seals.INSTALL
seals.INSTALL = seals.INSTALL.replace(old, new)
source = Path('TCSlib/Complexity/Randomized/Build/IterateFind.lean').read_text()
folder = Path('evidence/seals/carrier-diagnostic')
folder.mkdir(parents=True, exist_ok=True)
manifest = []
for mode in ['A', 'B']:
    label = 'carrier-diagnostic_' + mode + '_strict'
    probe, mapping, offset = seals.prepare(source, label, mode, False)
    destination = folder / (mode + '_strict.lean')
    destination.write_text(probe)
    destination.with_suffix('.linemap.json').write_text(json.dumps(mapping) + '\n')
    manifest.append(dict(source='TCSlib/Complexity/Randomized/Build/IterateFind.lean',
        probe=str(destination), label=label, mode=mode, coe=False, source_offset=offset,
        diagnostic_only=True, exclusions=['Turing.ModuleHost.hostTM', 'Complexity.IterateFind.copyTM']))
(folder / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
(folder / 'order.txt').write_text(''.join(item['probe'][:-5] + '\n' for item in manifest))
print('Prepared two NON-CANONICAL carrier-localization diagnostics')
