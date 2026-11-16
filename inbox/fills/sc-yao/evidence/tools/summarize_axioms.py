#!/usr/bin/env python3
"""Parse all-stored constant traces without dropping multiline Lean arrays."""
import argparse
import json
from pathlib import Path
import re

p = argparse.ArgumentParser()
p.add_argument('--run', required=True)
p.add_argument('--output', required=True)
p.add_argument('--simulators-proved', action='store_true')
a = p.parse_args()
rows = [json.loads(s) for s in
        (Path('evidence/probe-runs') / a.run / 'results.jsonl').read_text().splitlines()]
assert len(rows) == 1
r = rows[0]
assert r['exit'] == r['errors'] == r['generic_errors'] == 0 and r['fresh_olean'], r
raw = Path(r['log']).read_text()
axioms, closures = {}, {}
for kind, name, arr in re.findall(r'^(AXIOMS|SORRY_CLOSURE)\t([^\t\n]+)\t\[([^\]]*)\]', raw, re.M):
    target = axioms if kind == 'AXIOMS' else closures
    assert name not in target, name
    target[name] = [s.strip() for s in arr.split(',') if s.strip()]
assert axioms.keys() == closures.keys()
count = int(re.search(r'STORED_CONSTANTS (\d+)', raw).group(1))
assert len(axioms) == count
standard = {'propext', 'Classical.choice', 'Quot.sound'}
helpers = {n for n in axioms if '.YaoHybridProof.' in n or '.Yao.HybridProof.' in n}
bad = {n:dict(axioms=axioms[n], sorry_closure=closures[n]) for n in helpers
       if set(axioms[n]) - standard or closures[n]}
assert not bad, bad
prefix = 'TCSlib.Cryptography.SecureComputation.'
targets = {n:dict(axioms=axioms[prefix+n], sorry_closure=closures[prefix+n]) for n in
           ['yaoHybrid_polyTime', 'yaoHybrid_simulators', 'yaoHybrid_hbcSecure',
            'yaoProtocol_hbcSecure']}
assert not targets['yaoHybrid_polyTime']['sorry_closure']
if a.simulators_proved:
    allowed = {prefix+'yaoSeed_good_whp', prefix+'sliceMultiMessageSecure_of_prfOut'}
    assert set(targets['yaoHybrid_simulators']['sorry_closure']) == allowed
    assert set(targets['yaoHybrid_hbcSecure']['sorry_closure']) == allowed
else:
    assert targets['yaoHybrid_simulators']['sorry_closure'] == [prefix+'yaoHybrid_simulators']
out = Path(a.output)
assert not out.exists(), out
out.write_text(json.dumps(dict(stored_constants=count, helper_stored_constants=len(helpers),
    helper_nonstandard_axioms_or_admissions=bad, targets=targets, log=r['log'],
    simulators_proved=a.simulators_proved), indent=2) + '\n')
print('ALL STORED TRACE PASS', count, 'constants;', len(helpers), 'helpers')
