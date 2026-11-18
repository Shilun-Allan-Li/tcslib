"""io-sprg root-only serial composition searches through the pinned no-o runner.
Materializer validates one public-only full example per probe. No source mutation.
"""
import json, subprocess
from pathlib import Path
root = Path.cwd()
packet = Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared')
rows = json.loads((packet/'overlap/public-core-index.json').read_text())
reuse = ['Bridge.expect_sample_pair; ProbComp.expect_bind/expect_pure',
    'ProbComp.expect_sample_comm composed for the specified three factors',
    'ProbComp.expect_sample_update; ProbComp.expect_sample_comm']
for core, row in enumerate(rows, 1):
    stem = Path(row['template']).name.removesuffix('.lean.template')
    name = 'M4LPNPublic_V1_' + stem
    for mode in ('exact', 'apply'):
        subprocess.run(['python3', '-I', 'evidence/tools/lpn-defs-overlap-v2/materialize_public_core.py',
            str(core), mode, '--tag', 'V1'], check=True)
        order = 'evidence/logs/overlap-' + name + '-' + mode + '.txt'
        subprocess.run(['python3', '-I', 'evidence/tools/seal/runner_full.py', '.',
            order, '.lake/io-sprg-oleans', 'evidence/overlap/runs'], check=True)
    subprocess.run(['python3', '-I', 'evidence/tools/record_overlap.py', name,
        '--reuse', reuse[core-1]], check=True)
