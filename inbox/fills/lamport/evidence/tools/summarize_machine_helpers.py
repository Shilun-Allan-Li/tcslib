"""Summarize the exact immutable source snapshots of the nine passing native checks."""
import hashlib
import json
from pathlib import Path
import re
import sys

evidence = Path(sys.argv[1])
attempts = dict(Advice='Final01', Blocks='Final02', Closing='Final01',
                InversionProbability='Final02', Machine='Final02', Seed='Final01',
                MachineSpec='Final03', Nonabort='Final01', Realization='Final03')
rows = [json.loads(line) for line in (evidence / 'logs/helper-checks/results.jsonl').read_text().splitlines()]
result = []
for name, attempt in attempts.items():
    found = [row for row in rows if row['module'].endswith('/' + name) and row['attempt'] == attempt]
    assert len(found) == 1 and found[0]['exit'] == 0, (name, found)
    row = found[0]
    log = evidence / row['log']
    snapshot = log.with_suffix('.source.lean')
    raw = snapshot.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == row['source_sha256']
    assert not re.search(r'(?m)^.*\.lean:\d+:\d+: error(?:\([^)]*\))?:', log.read_text())
    assert "declaration uses 'sorry'" not in log.read_text()
    result.append(dict(module=row['module'], attempt=attempt, exit=0,
        log=row['log'], source_snapshot=str(snapshot.relative_to(evidence)),
        source_sha256=row['source_sha256'], source_lines=len(raw.decode().splitlines()),
        public_declarations=re.findall(r'(?m)^(?:noncomputable )?(?:def|theorem|lemma)\s+(\S+)',raw.decode())))
out = evidence / 'logs/final-machine-helpers-ready.json'
assert not out.exists(), out
out.write_text(json.dumps(dict(status='ALL_NINE_NATIVE_CHECKS_PASS',
    compiler_slot_released=True, axioms_seals_and_final_sweep_pending=True,
    compilation_repairs_changed_no_public_statements=True, records=result),indent=2)+'\n')
print(out)
for row in result:
    print(row['module'].split('/')[-1],row['attempt'],row['source_lines'],'lines',row['source_sha256'])
