#!/usr/bin/env python3
"""Refresh final sources and select only the new/doc-changed seals plus controls/trace."""
import json
from pathlib import Path
import subprocess
names = ['RunWithHost', 'Decryption', 'FirstTagged', 'EvalGate', 'GarbledRun', 'BobTables']
files = ['TCSlib/Cryptography/SecureComputation/Yao/HybridProof/' + name + '.lean'
         for name in names]
for phase in ['base', 'final']:
    subprocess.run(['python3', '-I', 'evidence/subagents/b/tools/make_seals.py', phase,
                    *files], check=True)
root = Path('evidence/subagents/b')
seals = json.loads((root/'seals/final/manifest.json').read_text())
selected = [r for r in seals if Path(r['file']).stem in ['RunWithHost', 'BobTables']]
selected += json.loads((root/'seals/controls/manifest.json').read_text())
selected += json.loads((root/'probes/manifest.json').read_text())
(root/'followup-manifest.json').write_text(json.dumps(selected, indent=2)+'\n')
print('Prepared', len(selected), 'sequential probes')
