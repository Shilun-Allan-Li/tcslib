#!/usr/bin/env python3
"""APFS-clone only completed TCSlib oleans; link the lead's read-only packages."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('agents', nargs='+', choices=['a', 'b', 'c'])
parser.add_argument('--label', required=True)
args = parser.parse_args()
lead = Path.cwd()
records = [json.loads(row)
           for path in sorted(Path('evidence/logs').glob('bootstrap*/results.jsonl'))
           for row in path.read_text().splitlines()]
modules = sorted({r['module'] for r in records
                  if not r['exit'] and not r['errors'] and not r['generic_errors']
                  and r['module'].startswith('TCSlib/')})
log = Path('evidence/subagents') / ('seed-' + args.label + '.jsonl')
log.parent.mkdir(parents=True, exist_ok=True)
assert not log.exists(), log
for name in args.agents:
    work = lead.parent.parent / ('sc-yao-' + name) / lead.name
    assert work.is_dir(), work
    (work / '.lake').mkdir(exist_ok=True)
    packages = work / '.lake/packages'
    if packages.is_symlink():
        assert packages.resolve() == (lead / '.lake/packages').resolve()
    elif packages.exists():
        raise RuntimeError('Refusing to replace package directory ' + str(packages))
    else:
        packages.symlink_to(lead / '.lake/packages', target_is_directory=True)
    ol = work / '.lake/sc-yao-oleans'
    for module in modules:
        src = lead / '.lake/sc-yao-oleans' / (module + '.olean')
        dst = ol / (module + '.olean')
        dst.parent.mkdir(parents=True, exist_ok=True)
        assert src.stat().st_size > 0, src
        subprocess.run(['cp', '-c', str(src), str(dst)], check=True)
        before = hashlib.sha256(src.read_bytes()).hexdigest()
        after = hashlib.sha256(dst.read_bytes()).hexdigest()
        assert before == after
        with log.open('a') as out:
            out.write(json.dumps(dict(agent=name, module=module, sha256=before)) + '\n')
    for relative in ['TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean',
                     'TCSlib/Complexity/CircuitComplexity/Uniform.lean',
                     'TCSlib/Cryptography/SecureComputation/Yao/HybridProof/CoinRead.lean']:
        target = work / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(lead / relative, target)
    print('SEEDED', name, len(modules), 'completed TCSlib modules; packages linked')
