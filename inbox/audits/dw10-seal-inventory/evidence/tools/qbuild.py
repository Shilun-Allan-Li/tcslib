# qbuild.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Variant deduplication and the seal run queue.
# Usage: python3 -I qbuild.py <evidence> <worktree> <out-queue> <out-dedup.json> <batch>... [--only <owners-file>]
# For each owner of the batches, reads the four seal records (seals/records/{strict-A,strict-B,coe-A,coe-B}/<batch>/) and the
# probe bytes, and decides which probes run (brief, suite item 2, "Variant deduplication"):
#   coe-A (canonical) always runs (DW10Probe/C/SealA_*);
#   strict-A runs unless its probe is byte-identical to coe-A's (same label SealA_: identical iff the request rows are);
#   coe-B runs unless its probe equals coe-A's after the label normalization SealB_ -> SealA_ (identical rows: PolyExpr.eval
#     not in the closure);
#   strict-B runs unless it is byte-identical to coe-B's, or equal to strict-A's after the same label normalization.
# Each record of dedup.json gives the variant, the probe SHA-256, the normalized SHA-256, and the run module whose result
# stands for it ("dedup_with"). Queue order: owners holding an input item first (checkpoint 1), then the batch order.
import sys, json, hashlib, os
ev, wt, outq, outd = sys.argv[1:5]; rest = sys.argv[5:]
only = None
if '--only' in rest:
    i = rest.index('--only'); only = {l.strip() for l in open(rest[i + 1]) if l.strip()}; rest = rest[:i] + rest[i + 2:]
batches = rest
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(ev, 'collect/batches.tsv'))][1:]
sha = lambda b: hashlib.sha256(b).hexdigest()
def rec(variant, batch, module):
    pre = 'SealB_' if variant.endswith('B') else 'SealA_'
    p = os.path.join(ev, 'seals/records', variant, batch, pre + module.split('.', 1)[1].replace('.', '_') + '.json')
    return json.load(open(p))
dedup, queue_hold, queue_rest = [], [], []
for b, module, path, tier, agent, pos, hold in rows:
    if b not in batches or (only is not None and module not in only): continue
    r = {v: rec(v, b, module) for v in ('coe-A', 'strict-A', 'coe-B', 'strict-B')}
    raw = {v: open(os.path.join(wt, r[v]['probe_module'] + '.lean'), 'rb').read() for v in r}
    norm = {v: raw[v].replace(r[v]['label'].encode(), r[v]['label'].replace('SealB_', 'SealA_').encode()) for v in r}
    run = {}
    run['coe-A'] = r['coe-A']['probe_module']
    run['strict-A'] = run['coe-A'] if raw['strict-A'] == raw['coe-A'] else r['strict-A']['probe_module']
    run['coe-B'] = run['coe-A'] if norm['coe-B'] == norm['coe-A'] else r['coe-B']['probe_module']
    if raw['strict-B'] == raw['coe-B']: run['strict-B'] = run['coe-B']
    elif norm['strict-B'] == norm['strict-A']: run['strict-B'] = run['strict-A']
    else: run['strict-B'] = r['strict-B']['probe_module']
    q = queue_hold if hold == 'yes' else queue_rest
    for v in ('coe-A', 'strict-A', 'coe-B', 'strict-B'):
        own = r[v]['probe_module']
        dedup.append(dict(batch=b, module=module, path=path, tier=tier, agent=agent, holds_input_item=hold, variant=v,
                          label=r[v]['label'], probe_module=own, probe_sha256=sha(raw[v]), normalized_sha256=sha(norm[v]),
                          requested=r[v]['requested'], run_module=run[v], dedup_with='-' if run[v] == own else run[v]))
        if run[v] == own and own not in q: q.append(own)
json.dump(dedup, open(outd, 'w'), indent=1)
open(outq, 'w').write(''.join(m + '\n' for m in queue_hold + queue_rest))
print('owners', len(dedup) // 4, 'probes', len(dedup), 'to run', len(queue_hold) + len(queue_rest), '(holders first:', len(queue_hold), ')')
