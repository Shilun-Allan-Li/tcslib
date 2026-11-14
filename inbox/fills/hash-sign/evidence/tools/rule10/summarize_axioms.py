"""Summarize all-stored-constant axiom output from the complete final collector."""
import argparse
import json
from pathlib import Path
import re

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--log', required=True, type=Path)
p.add_argument('--out', required=True, type=Path)
args = p.parse_args()
text = args.log.read_text()
rows = []
for line in text.splitlines():
    if line.startswith('AXIOMS '):
        home, name, axioms = line[7:].split(' | ')
        rows.append({'home': home, 'name': name, 'axioms': [] if axioms == '[]' else axioms.strip('[]').split(', ')})
owners = (args.out / 'owners.txt').read_text().splitlines()
counts = {m: 0 for m in owners}
for row in rows:
    counts[row['home']] += 1
declared = re.findall(r'^AXIOMS-STORED-COUNT (\d+)$', text, re.M)
if len(declared) != 1 or int(declared[0]) != len(rows):
    raise RuntimeError('all-constant axiom count differs')
if len({row['name'] for row in rows}) != len(rows):
    raise RuntimeError('duplicate stored constant')
standard = {'propext', 'Classical.choice', 'Quot.sound'}
summary = {'stored_constants': len(rows), 'by_owner': counts,
           'outside_standard_axioms': [r for r in rows if set(r['axioms']) - standard],
           'target': [r for r in rows if r['name'] == 'TCSlib.Cryptography.Authentication.hashAndSign_oneTimeSecure']}
(args.out / 'axioms-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary))
