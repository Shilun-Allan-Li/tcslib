"""Root-only one-helper sorry ladder from an explicit reviewed JSON specification.

No Lean. Requires archived exact/apply overlap records; proof_step archives and
inserts exactly one complete tactic block. Existing statements are never changed.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import textwrap

ap = argparse.ArgumentParser()
ap.add_argument('specs')
ap.add_argument('name')
a = ap.parse_args()
rows = json.loads(Path(a.specs).read_text())
matches = [r for r in rows if r['name'] == a.name]
assert len(matches) == 1
r = matches[0]
search = json.loads(Path('evidence/overlap/probes', r['probe'], 'search.json').read_text())
assert {s['mode'] for s in search['searches']} == {'exact', 'apply'}
assert all(s['status'] != 'INVALID_ELABORATION' for s in search['searches'])
candidate = Path(r['candidate']).read_text()
start = re.search(r'^theorem ' + re.escape(a.name) + r'(?=\s|\(|\{|:)', candidate, re.M)
assert start
tail = candidate[start.start():]
m = re.search(r':=\s+by\n', tail)
assert m
header, body = tail[:m.start()].rstrip(), 'by\n' + tail[m.end():].rstrip() + '\n'
owner = Path(r['file'])
assert str(owner).startswith('TCSlib/Cryptography/Obfuscation/StructuredSeed/')
source = owner.read_text()
assert not re.search(r'^theorem ' + re.escape(a.name) + r'\b', source, re.M)
marker = r.get('marker', ('\nend TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal\n'
          if owner.stem == 'Bounds' else '\nend Internal\n'))
assert source.count(marker) == 1
doc = '\n\n'.join(textwrap.fill(p, width=92) for p in r['doc'].split('\n\n'))
stub = '\n/-- ' + doc + ' -/\n' + header + ' := sorry\n'
owner.write_text(source.replace(marker, stub + marker))
proof = Path('evidence/proof-candidates/installed-helpers', a.name + '.proof')
proof.parent.mkdir(parents=True, exist_ok=True)
assert not proof.exists()
proof.write_text(body)
subprocess.run(['python3', '-I', 'evidence/tools/proof_step.py', str(owner),
                a.name, str(proof)], check=True)
