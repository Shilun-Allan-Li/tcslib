"""Compare actual declaration-level sorry warnings with the issued baseline."""
import argparse
import json
from pathlib import Path
import re
import runpy
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('tree')
parser.add_argument('phase')
parser.add_argument('--removed', action='append', default=[])
args = parser.parse_args()
tree = Path(args.tree).resolve()
scanner = runpy.run_path(str(Path(__file__).with_name('frozen_headers.py')))
expected = set()
for line in Path('evidence/inputs/issued/outbox/fills/derand-r2/base-sorries.txt').read_text().splitlines():
    if not line.strip() or line.startswith('TOTAL '):
        continue
    module, number, names = line.split(': ', 2)
    module = module if module.startswith('TCSlib/') else 'TCSlib/Complexity/' + module
    declarations = names.split(', ')
    assert len(declarations) == int(number)
    expected.update((module, name) for name in declarations)
removed = {item for item in expected if item[1] in args.removed}
assert {name for _, name in removed} == set(args.removed)
expected -= removed
rows = [json.loads(line) for line in (tree / 'evidence/logs' / args.phase / 'results.jsonl').read_text().splitlines()]
actual, warning_rows = set(), []
for row in rows:
    assert row['exit'] == 0 and row['errors'] == 0, row
    module = row['module']
    if not module.startswith('TCSlib/'):
        continue
    log = (tree / row['log']).read_text()
    warnings = re.findall(r'^\S+\.lean:(\d+):\d+: warning: declaration uses .sorry.', log, re.M)
    if not warnings:
        continue
    if row.get('source_sha256'):
        source = (tree / 'evidence/sources' / (row['source_sha256'] + '.lean')).read_text()
    else:
        source = subprocess.check_output(['git', 'show', f'{scanner["BASE"]}:{module}.lean'], text=True)
    matches = list(scanner['DECL'].finditer(scanner['mask'](source)))
    declarations = [(source.count('\n', 0, match.start()) + 1, match['name']) for match in matches]
    for raw_line in warnings:
        line_number = int(raw_line)
        name = next(name for start, name in reversed(declarations) if start <= line_number)
        actual.add((module, name))
        warning_rows.append(dict(module=module, name=name, line=line_number, log=row['log']))
missing, extra = expected - actual, actual - expected
out = Path('evidence/sorries') / args.phase
out.mkdir(parents=True, exist_ok=True)
record = dict(phase=args.phase, tree=str(tree), checked_modules=len(rows),
              removed=sorted(removed), actual=sorted(actual), missing=sorted(missing),
              extra=sorted(extra), warnings=warning_rows)
(out / 'results.json').write_text(json.dumps(record, indent=2) + '\n')
print(f'{args.phase}: {len(rows)} successful modules; {len(actual)} sorry declarations '
      f'in {len({module for module, _ in actual})} modules')
print(f'Missing expected={len(missing)}; unexpected={len(extra)}; removed={sorted(removed)}')
print('SORRY BASELINE ' + ('PASS' if not missing and not extra else 'FAIL'))
raise SystemExit(bool(missing or extra))
