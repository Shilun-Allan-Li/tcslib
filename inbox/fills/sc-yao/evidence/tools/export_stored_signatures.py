#!/usr/bin/env python3
"""Export complete elaborated types from the immutable all-stored Lean output."""
import argparse
import hashlib
import json
from pathlib import Path
import re

p = argparse.ArgumentParser()
p.add_argument('--run', required=True)
p.add_argument('--ref', required=True)
p.add_argument('--output', required=True)
a = p.parse_args()
records = [json.loads(s) for s in (Path('evidence/probe-runs') / a.run /
                                 'results.jsonl').read_text().splitlines()]
assert len(records) == 1
record = records[0]
assert record['exit'] == record['errors'] == record['generic_errors'] == 0
log = Path(record['log'])
raw = log.read_text()
types = {}
for match in re.finditer(r'^SIGNATURE\t([^\t\n]+)\t', raw, re.M):
    name = match.group(1)
    stop = raw.index("\n'" + name + "' ", match.end())
    ty = raw[match.end():stop].rstrip()
    assert ty and name not in types
    types[name] = ty
count = int(re.search(r'STORED_CONSTANTS (\d+)', raw).group(1))
assert len(types) == count
out = Path(a.output)
assert not out.exists()
out.parent.mkdir(parents=True, exist_ok=True)
heading = ('# Fully elaborated stored signatures\n\n'
    f'Proof source ref: `{a.ref}`. This file exports all {count} complete Lean types,\n'
    'including implicit section parameters and private/generated constants. The raw\n'
    f'authoritative output is `{record["log"]}`; SHA256 '
    f'`{hashlib.sha256(log.read_bytes()).hexdigest()}`.\n\n'
    'These are elaborated type displays, rather than source-header lexer excerpts.\n\n')
out.write_text(heading + '\n'.join('## `' + n + '`\n\n```lean\n' + n + ' : ' + ty +
    '\n```\n' for n, ty in sorted(types.items())))
out.with_suffix('.json').write_text(json.dumps(dict(ref=a.ref, stored_constants=count,
    log=record['log'], signatures=types), indent=2) + '\n')
print('EXPORTED', count, 'complete stored types to', out)
