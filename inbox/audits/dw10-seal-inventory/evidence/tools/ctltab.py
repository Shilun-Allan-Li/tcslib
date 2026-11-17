# ctltab.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. The brief's evidence/controls.tsv, one row per owner:
# path, tier, agent, status (pair / negative only / defines nothing / no passing candidate), definition, reader (or `no reader`),
# reader note, negative result (sealed strict / sealed coe / unsealed: errors in its lines), positive result, harness, ALL_OK of
# the harness in strict and coe (ctlcheck2.py over plan-strict.json and plan-coe.json).
# "negative only": every reader candidate of the owner failed the unsealed `intros; rfl` pretest (the reader is not a
# definitional equation), so the eq_def negative runs alone and the row records `no reader` with the note
# "readers exist, none rfl-checkable" (brief: "no reader" is check 8 debt, not a seal failure).
# Usage: python3 -I ctltab.py <evidence> <out.tsv>
import sys, os, json, csv
ev, outp = sys.argv[1:3]; C = os.path.join(ev, 'controls/final')
chosen = json.load(open(os.path.join(C, 'chosen.json'))); cand = json.load(open(os.path.join(ev, 'controls/pretest/candidates.json')))
ck = {k: json.load(open(os.path.join(C, f'ctlcheck-{k}.json'))) for k in ('strict', 'coe') if os.path.exists(os.path.join(C, f'ctlcheck-{k}.json'))}
res = {}
for k, d in ck.items():
    for p in d['probes']:
        for c in p['controls']: res[(p['label'], c['control'])] = c
okh = {k: {p['label']: p['ok'] for p in d['probes']} for k, d in ck.items()}
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(ev, 'collect/batches.tsv'))][1:]
out = []
for b, m, path, tier, agent, *_ in rows:
    v = chosen.get(m); c = v['pick'] if v else None
    if not v or not c:
        st = v['status'] if v else '-'; out.append([path, tier, agent, st] + ['-'] * 9); continue
    g = v['group']; k = [x for x in rows if x[0] == b].index(next(x for x in rows if x[1] == m)) % 25
    tag = f"c{g}_{k}_{v['pick_index']}"
    has_r = any(x['reader'] for x in cand[m]['candidates'])
    def r(lbl, ctl): x = res.get((lbl, ctl)); return f"{x['errors']}/{x['expected']}" if x else 'not run'
    neg = f"strict {r('ControlS_' + g, tag + '_neg')}, coe {r('ControlC_' + g, tag + '_neg')}, unsealed {r('ControlU_' + g, tag + '_neg')}"
    pos = (f"strict {r('ControlS_' + g, tag + '_pos')}, coe {r('ControlC_' + g, tag + '_pos')}, unsealed {r('ControlU_' + g, tag + '_pos')}" if c['reader'] else '-')
    out.append([path, tier, agent, 'pair' if c['reader'] else 'negative only', c['target'], c['reader'] or 'no reader',
                '-' if c['reader'] else ('readers exist, none rfl-checkable' if has_r else 'no reader candidate'), neg, pos, g,
                str(okh.get('strict', {}).get('ControlS_' + g, '-')), str(okh.get('coe', {}).get('ControlC_' + g, '-')), tag])
H = ['path', 'tier', 'agent', 'status', 'definition', 'reader', 'note', 'negative (errors/expected)', 'positive (errors/expected)', 'harness', 'ALL_OK_strict_harness', 'ALL_OK_coe_harness', 'control_tag']
open(outp, 'w').write('\t'.join(H) + '\n' + ''.join('\t'.join(x) + '\n' for x in out))
import collections
print(collections.Counter(x[3] for x in out))
