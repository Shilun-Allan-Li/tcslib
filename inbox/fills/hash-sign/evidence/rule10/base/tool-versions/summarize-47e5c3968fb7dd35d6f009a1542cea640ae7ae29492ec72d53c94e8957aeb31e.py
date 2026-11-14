"""Summarize completed Rule-10 probes and list only their closed raw logs."""
import argparse
import hashlib
import json
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--out', required=True, type=Path)
parser.add_argument('--collector-log', type=Path)
parser.add_argument('--resource-log', action='append', default=[], type=Path)
args = parser.parse_args()
rows = [json.loads(line) for line in (args.out / 'results.jsonl').read_text().splitlines() if line]
seals, controls, pairs = [], [], {}
for row in rows:
    if '/Seal' in row['module']:
        seals.append({k: row[k] for k in ['module', 'label', 'rc', 'error_count', 'failing_declarations', 'raw_log']})
    if row.get('expected_error_count') is not None:
        controls.append(row)
        match = re.search(r'/Control(?:Foreign|Singleton)([AB])([SU])_(.+)$', row['module'])
        if match:
            pair = pairs.setdefault(match[1] + ':' + match[3], {})
            pair['sealed' if match[2] == 'S' else 'unsealed'] = {'label': row['label'], 'expectation_passed': row['expectation_passed'],
                'error_count': row['error_count'], 'raw_log': row['raw_log'],
                'failing_declaration': 'HashSignSensitivity.negative' if match[2] == 'S' else None}
for pair in pairs.values():
    pair['passed'] = all(k in pair and pair[k]['expectation_passed'] for k in ['sealed', 'unsealed'])
closed = {Path(r['raw_log']) for r in rows}
collector = None
if args.collector_log:
    text = args.collector_log.read_text()
    if not re.search(r'end: .* exit: 0\s*$', text):
        raise SystemExit('collector log is not a completed successful check')
    closed.add(args.collector_log)
    collector = {'raw_log': str(args.collector_log), 'stored_constant_count': len(re.findall(r'^AXIOMS ', text, re.M)),
          'constants_with_sorryAx': [line for line in text.splitlines() if line.startswith('AXIOMS ') and 'sorryAx' in line]}
for p in args.resource_log:
    closed.add(p)
logs = [{'path': str(p), 'bytes': p.stat().st_size, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(closed)]
summary = {'collector': collector, 'seals': seals, 'paired_controls': pairs,
           'control_probe_count': len(controls), 'all_control_expectations_passed': all(r['expectation_passed'] for r in controls),
           'all_pairs_complete_and_passed': bool(pairs) and all(p['passed'] for p in pairs.values()),
           'closed_raw_logs': logs}
(args.out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
(args.out / 'closed-log-list.txt').write_text(''.join(r['path'] + '\n' for r in logs))
print(json.dumps({k: v for k, v in summary.items() if k not in ['collector', 'paired_controls', 'closed_raw_logs']}))
