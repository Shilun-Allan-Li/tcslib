#!/usr/bin/env python3
"""Classify the residual whole-file seal diagnostics of the final head (standard variant) into
escalation/incomplete classes, per failing declaration.

python3 -I classify_residual.py <phase> <out-blocked.json> <out-summary.md>
(reads evidence/logs/seal-<phase>.json and the full error texts of its module logs)

Classes (first matching rule wins, per declaration):
* PROVIDER_FROZEN — the file is PROVIDER_ONLY: its proofs may not change (role rule); the
  failure needs a provider proof/body change (E-FREEZE) or a new non-reader contract (E-API).
* E_API_INLINE_MATCH — a diagnostic shows a provider contract whose function is an inline `match`
  (on `pairDecode` or `List.find?`): the consumer's own function can only be identified with it
  through the foreign compiler-generated matcher (sealed) or its generated equations (C3); the
  missing contract is the provider theorem restated over a named, reader-equipped function.
* OPEN_MACHINE_INTERNALS — machine-model/host-state internals (`ModuleHost.State`,
  `FinTM.State`, `padTM`, `stopCfg`, `emitCfg`, decoded-code machine fields) read by conversion;
  not analysed further in this session (whether ordinary field/run readers suffice or a new host
  contract would be needed is open).
* OPEN_TYPED_COINS — the coin/seed type of a constructed machine or structure-valued definition
  (`.Coins n`, `ExecCoins`, `.σ n`, `Fin (… .coinLen n)`) is identified with a concrete type by
  conversion; repairable through the published equivalences (`NUPPT.coinsCongr`,
  `coinsEquivPoly`, `_domEquiv`) but not done.
* OPEN_INCOMPLETE — any other definitional read; repairable through existing or ordinary owner
  readers but not done in this session."""
import sys, json, re, collections
phase, outb, outm = sys.argv[1:4]
EV = '/workspace/cp2/evidence/logs'
sealf = f'{EV}/seal-{phase}.json'
def fulltexts(path):
    """error line in probe -> full error text (all lines up to the next diagnostic)."""
    rel = f'.lake/cleanup-part2-probes/seal/{phase}/{path}'
    log = open(f'{EV}/seal-{phase}/modules/{rel}.log').read()
    out = collections.defaultdict(list)
    for part in re.split(r'(?m)^(?=\S*\.lean:\d+:\d+: )', log):
        m = re.match(r'\S*\.lean:(\d+):(\d+): error[^:]*: ?', part)
        if m: out[int(m.group(1))].append(part[m.end():].split('CP2-EOF')[0])
    return out
PACK = '/workspace/tcslib/outbox/fills/cleanup-part2/inputs'
prov = {l.strip()[:-5] for l in open(f'{PACK}/provider-only-files.txt') if l.strip()}
seal = json.load(open(sealf))
res = {}
for path, r in seal.items():
    ft = fulltexts(path) if r['diagnostics'] else {}
    by = collections.defaultdict(list)
    for d in r['diagnostics']:
        by[(d['decl'], d['decl_line_in_source'])].append(d)
    for (decl, line), ds in by.items():
        texts = [t for d in ds for t in ft.get(d['error_line'], [d['message']])]
        full = ' '.join(texts)
        def inline_match(t):
            for m in re.finditer(r'\bmatch\b', t):
                p = m.start()
                if re.search(r'pairDecode|find\?', t[p:p + 90]) and \
                        re.search(r'ComputesFunInTime|PolyTimeComputable', t[max(0, p - 160):p]):
                    return True
            return False
        if path in prov: c = 'PROVIDER_FROZEN'
        elif any(inline_match(t) for t in texts): c = 'E_API_INLINE_MATCH'
        elif re.search(r'ModuleHost\.State|FinTM\.State|padTM|stopCfg|padCfg|emitCfg|\.State\b', full): c = 'OPEN_MACHINE_INTERNALS'
        elif re.search(r'Coins\b|ExecCoins|coinLen|\.σ\b', full): c = 'OPEN_TYPED_COINS'
        else: c = 'OPEN_INCOMPLETE'
        res[f'{path}.lean::{decl}@{line}'] = {'class': c, 'path': path + '.lean', 'decl': decl,
                                             'decl_line': line,
                                             'diagnostics': [f"{d['error_line_in_source']}: {d['message']}" for d in ds]}
json.dump(res, open(outb, 'w'), indent=1)
cnt = collections.Counter(v['class'] for v in res.values())
lines = ['# Residual seal failures at the final head, by class', '',
         '| class | failing declarations |', '|---|---|'] + [f'| {k} | {v} |' for k, v in sorted(cnt.items())]
lines += ['', '## By file', '']
byf = collections.defaultdict(collections.Counter)
for v in res.values(): byf[v['path']][v['class']] += 1
for f in sorted(byf):
    lines.append(f'* `{f}`: ' + ', '.join(f'{k} {n}' for k, n in sorted(byf[f].items())))
open(outm, 'w').write('\n'.join(lines) + '\n')
print(dict(cnt))
