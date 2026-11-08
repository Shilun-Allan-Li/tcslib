#!/usr/bin/env python3
"""Summarise a checks-<phase>.jsonl: last record per module, counts by status, failures, skips,
peak RSS, total elapsed. python3 -I checks_summary.py <jsonl> <out.json>"""
import sys, json, collections
recs = [json.loads(l) for l in open(sys.argv[1])]
last = {}
for r in recs: last[r['module']] = r
st = collections.Counter(r.get('status') for r in last.values())
res = {'records': len(recs), 'modules': len(last), 'status_counts': dict(st),
       'failures': [r['module'] for r in last.values() if r.get('status') == 'FAIL'],
       'skipped': [{'module': r['module'], 'missing': r.get('missing')} for r in last.values() if r.get('status', '').startswith('SKIPPED')],
       'superseded_records': len(recs) - len(last),
       'max_rss_kib': max((r.get('maxrss_kib') or 0) for r in recs),
       'total_elapsed_s': round(sum((r.get('elapsed_s') or 0) for r in recs), 1),
       'slowest': sorted(((r.get('elapsed_s') or 0, r['module']) for r in recs), reverse=True)[:5]}
json.dump(res, open(sys.argv[2], 'w'), indent=1)
print(json.dumps({k: v for k, v in res.items() if k not in ('skipped',)}, indent=1)[:1500])
