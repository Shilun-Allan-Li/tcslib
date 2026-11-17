"""Gate 149: citation homes (G147-02). Reads Cite_<stem>.log (#kinds per identifier, one block per
scope) and cite-idents.json; reports the TCSlib modules that define constants the changed or added
declarations cite at head but not at base, excluding the owners themselves."""
import json, re
from pathlib import Path
import os as _os
G = Path(_os.environ['GATE']); D = G/'dsw/TCSlib/Scratch/DefSweep'
idents = json.loads((D/'cite-idents.json').read_text())
owners = {p[:-5].replace('/', '.') for p in idents}
out = {'owners': sorted(owners), 'per_owner': {}, 'homes': {}}
for path, sides in idents.items():
    stem = Path(path).stem
    ids = sorted(set(sides['head']) | set(sides['base']))
    rows = [l.strip().split('|') for l in (G/'defsweep'/f'Cite_{stem}.log').read_text().splitlines() if l.strip().startswith('KIND|')]
    if not ids: out['per_owner'][path] = {'identifiers': 0}; continue
    assert len(rows) % len(ids) == 0, (path, len(rows), len(ids))
    res = {}
    for i, r in enumerate(rows):
        a = ids[i % len(ids)]
        if a not in res and r[2] not in ('unresolved', 'missing'):
            res[a] = (r[1], r[2], r[3])
    cited = lambda side: {res[a] for a in sides[side] if a in res}
    new = sorted(c for c in cited('head') - cited('base')
                 if c[2].startswith('TCSlib') and c[2] not in owners)
    out['per_owner'][path] = {'identifiers': len(ids), 'resolved': len(res), 'newly_cited_foreign': [list(c) for c in new]}
    for n, k, m in new:
        out['homes'].setdefault(m.replace('.', '/') + '.lean', []).append(n)
out['homes'] = {k: sorted(set(v)) for k, v in sorted(out['homes'].items())}
(G/'defsweep/CITATION-HOMES.json').write_text(json.dumps(out, indent=1) + '\n')
print(json.dumps({k: len(v) for k, v in out['homes'].items()}, indent=1))
