#!/usr/bin/env python3
"""Transfer the checked complete body, preserving the frozen source outside allowed spans."""
import argparse
import hashlib
import json
from pathlib import Path
import runpy

p = argparse.ArgumentParser()
p.add_argument('--install', action='store_true')
a = p.parse_args()
lex = runpy.run_path('evidence/tools/header_lexer.py')
path = Path('TCSlib/Cryptography/SecureComputation/Yao.lean')
source = path.read_text()
prototype = Path('evidence/subagents/a12/probes/CompleteSimulators.lean')
assert hashlib.sha256(prototype.read_bytes()).hexdigest() == (
    '2438566d0ccd1ec9b4b40e1e12b4d4dc5fc4e98f1db5741e1603d4c079b7d300')
proof = prototype.read_text()
d = next(d for d in lex['declarations'](proof) if d['name'] == 'simulators_complete')
body = proof[d['cut']:d['end']]
assert body.startswith(':= by\n  classical')
body = body.replace(':= by\n', ':= by\n  open YaoHybridProof in\n', 1)
target = next(d for d in lex['declarations'](source) if d['name'] == 'yaoHybrid_simulators')
assert source[target['cut']:target['end']] == ':= by\n  sorry'
sketch_start = source.index('**Proof sketch.**', *target['doc_range'])
sketch = Path('evidence/subagents/a10/SHORT-SKETCH.md').read_text().strip()
sketch = sketch.replace('two stages per gate', 'two substeps per gate')
old_bullet = '''* `SecureComputation.yaoSeed_good_whp`, `yaoHybrid_simulators` (stated; `sorry`s under sketches):
  the garbling is good w.h.p. and the simulators of Theorem 163.7.
'''
new_bullet = '''* `SecureComputation.yaoHybrid_simulators` (proved modulo sc-garble): the simulators of
  Theorem 163.7 in the OT-hybrid model.
* `SecureComputation.yaoSeed_good_whp` (stated; `sorry` under a sketch): the garbling is good
  with high probability.
'''
assert source.count(old_bullet) == 1
start = source.index(old_bullet)
spans = [(target['cut'], target['end'], body),
         (sketch_start, target['doc_range'][1] - 2, sketch + ' '),
         (start, start + len(old_bullet), new_bullet)]
for begin, end, replacement in sorted(spans, reverse=True):
    source = source[:begin] + replacement + source[end:]
lines = source.splitlines()
assert len(lines) + 28 <= 1200
assert max(map(len, lines)) <= 100
dest = Path('evidence/development/FinalYaoCandidate.lean')
if a.install:
    assert dest.read_text() == source
    path.write_text(source)
else:
    assert not dest.exists()
    dest.write_text(source)
metrics = dict(installed=a.install, candidate=str(dest), lines=len(lines),
    combined_sc_garble_lines=len(lines) + 28, width_max=max(map(len, lines)),
    proof_body_lines=len(body.splitlines()) - 1,
    sha256=hashlib.sha256(source.encode()).hexdigest())
out = Path('evidence/logs/final-body-installed.json' if a.install else
           'evidence/logs/final-body-prepared.json')
assert not out.exists()
out.write_text(json.dumps(metrics, indent=2) + '\n')
print(json.dumps(metrics))
