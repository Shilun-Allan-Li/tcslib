"""Run both prescribed linters and diff their FAIL/WARN line sets."""
import json
from pathlib import Path
import re
import subprocess

def lines(path):
    rows = set()
    for line in Path(path).read_text().splitlines():
        match = re.match(r'^(FAIL|WARN)\s+(\S+)\s+(.*)$', line)
        if match:
            rows.add(match.groups())
    return rows

records = []
for corpus, expected in [('complexity', (25, 391)), ('cryptography', (92, 101))]:
    base = Path('evidence/logs') / ('lint-base-' + corpus + '.log')
    final = Path('evidence/logs') / ('lint-final-' + corpus + '.log')
    command = ['python3', '-I', 'scripts/campaign_style_lint.py',
               'TCSlib/' + corpus.capitalize(), '--check8b']
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    final.write_text(result.stdout)
    before, after = lines(base), lines(final)
    counts = lambda rows: tuple(sum(row[0] == level for row in rows) for level in ['FAIL', 'WARN'])
    assert counts(before) == expected, (corpus, counts(before))
    added, removed = sorted(after - before), sorted(before - after)
    new_fail = [row for row in added if row[0] == 'FAIL']
    exceptions = []
    for level, path, message in added:
        if level != 'WARN':
            continue
        allowed = path == 'TCSlib/Complexity/Randomized/Classes.lean' and (
            message == '1415 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)'
            or message == '2 public def(s) without a lemma beside them (check 8): InBPPStrong, InCoRP')
        exceptions.append(dict(line=(level, path, message), allowed=allowed,
            justification='SR-01 approved inherited size / reduced missing-reader warning' if allowed else 'UNREVIEWED'))
    row = dict(corpus=corpus, command=command, exit=result.returncode,
               base_counts=counts(before), final_counts=counts(after),
               added=added, removed=removed, new_fail=new_fail, warn_changes=exceptions)
    records.append(row)
    print(f'{corpus}: base={counts(before)} final={counts(after)} '
          f'added FAIL={len(new_fail)} added WARN={len(exceptions)}')
    for item in added:
        print('  ADDED ' + ' '.join(item))
    for item in removed:
        print('  REMOVED ' + ' '.join(item))
out = Path('evidence/lint')
out.mkdir(parents=True, exist_ok=True)
(out / 'line-set-diff.json').write_text(json.dumps(records, indent=2) + '\n')
ok = all(not row['new_fail'] and all(item['allowed'] for item in row['warn_changes']) for row in records)
print('LINT LINE-SET DIFF ' + ('PASS' if ok else 'FAIL'))
raise SystemExit(not ok)
