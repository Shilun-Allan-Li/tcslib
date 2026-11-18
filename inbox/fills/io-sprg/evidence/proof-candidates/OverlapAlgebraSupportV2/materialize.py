#!/usr/bin/env python3
"""Materialize ONE isolated overlap probe; never invokes Lean or another process."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('name')
parser.add_argument('--tactic', choices=['exact?', 'apply?'], required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
base = Path(__file__).resolve().parent
index = {row['name']: row for row in json.loads((base / 'probe-index.json').read_text())}
if args.name not in index:
    parser.error('unknown probe name')
destination = Path(args.output).resolve()
if not destination.is_relative_to(Path('/private/tmp').resolve()):
    parser.error('output must be under /private/tmp (or its /tmp alias)')
source = (base / index[args.name]['template']).read_text()
if source.count('__PROBE_BODY__') != 1:
    raise RuntimeError('template must contain exactly one body placeholder')
result = source.replace('__PROBE_BODY__', 'by\n  classical\n  ' + args.tactic)
if result.count(':= by') != 1:
    raise RuntimeError('materialization must introduce exactly one tactic block')
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(result)
print(json.dumps({'probe': args.name, 'tactic': args.tactic, 'output': str(destination),
                  'Lean_executed': False, 'tactic_blocks_introduced': 1}))
