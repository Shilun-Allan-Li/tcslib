# bb1-sim-statements (lead): copied unchanged from the bb1-machine delivery.
"""ctlcheck.py <plan.json> <rundir> <out.json>: verify control outcomes (unsealed rc 0; sealed: exactly one
error inside each negative control, none in positives, no harness error, seal install+EOF records)."""
import sys, json, re
plan = json.load(open(sys.argv[1])); rd = sys.argv[2]; out = []
res = {}
for l in open(f'{rd}/results.jsonl'):
    x = json.loads(l)
    if 'module' in x: res[x['module']] = x
ok_all = True
for p in plan:
    r = res.get(p['module']); log = open(f"{rd}/mods/{p['module'].replace('/', '_')}.log", encoding='utf-8', errors='replace').read()
    errs = [int(m.group(1)) for m in re.finditer(r'^\S+\.lean:(\d+):\d+: error[:(]', log, re.M)]
    per = []
    for c in p['controls']:
        n = sum(1 for e in errs if c['start_line'] <= e <= c['end_line'])
        exp = 1 if (p['sealed'] and c['negative']) else 0
        per.append(dict(control=c['control'], target=c['target'], negative=c['negative'], errors=n, expected=exp, ok=n == exp))
    stray = [e for e in errs if not any(c['start_line'] <= e <= c['end_line'] for c in p['controls'])]
    inst = bool(re.search(r'G06-SEAL label=' + re.escape(p['label']), log)); eof = bool(re.search(r'G06-SEAL-END label=' + re.escape(p['label']), log))
    ok = all(x['ok'] for x in per) and not stray and ((r['rc'] == 1 and inst and eof) if p['sealed'] else r['rc'] == 0)
    ok_all &= ok
    out.append(dict(label=p['label'], owner=p['owner'], kind=p['kind'], sealed=p['sealed'], rc=r['rc'], requested=p['requested'],
                    install_record=inst, eof_record=eof, stray_errors=stray, controls=per, ok=ok))
json.dump(dict(all_ok=ok_all, probes=out), open(sys.argv[3], 'w'), indent=1)
for o in out: print(('PASS' if o['ok'] else 'FAIL'), o['label'], 'rc', o['rc'], [(c['control'], c['errors']) for c in o['controls']], o['stray_errors'])
print('ALL_OK', ok_all)
