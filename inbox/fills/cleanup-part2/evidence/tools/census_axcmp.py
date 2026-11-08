#!/usr/bin/env python3
"""Compare two census axiom tables (`AXIOMS\t<module>\t<name>\t[axioms]`) by unique
(module, actual Name) identity (cleanup-part2).

python3 -I census_axcmp.py <base axioms.tsv> <head axioms.tsv> <out.json>

Reports: identities only at base (removed/moved away), only at head (added/moved in), names whose
home module changed (moved), identities whose axiom set changed, sorryAx-bearing identities at
both ends, and the axiom-set histograms. Raw multiplicities are kept (a repeated identity is
counted per row)."""
import sys, json, collections
def load(p):
    rows = []
    for line in open(p):
        if not line.startswith('AXIOMS\t'): continue
        _, mod, name, ax = line.rstrip('\n').split('\t', 3)
        rows.append((mod, name, tuple(sorted(a.strip() for a in ax.strip('[]').split(',') if a.strip()))))
    return rows
B, H = load(sys.argv[1]), load(sys.argv[2])
cb = collections.Counter((m, n) for m, n, _ in B); ch = collections.Counter((m, n) for m, n, _ in H)
axb = {(m, n): a for m, n, a in B}; axh = {(m, n): a for m, n, a in H}
nb = collections.defaultdict(set); nh = collections.defaultdict(set)
for m, n, _ in B: nb[n].add(m)
for m, n, _ in H: nh[n].add(m)
only_b = sorted(set(axb) - set(axh)); only_h = sorted(set(axh) - set(axb))
moved = sorted(n for n in set(nb) & set(nh) if nb[n] != nh[n])
changed = sorted(k for k in set(axb) & set(axh) if axb[k] != axh[k])
res = {
    'base_rows': len(B), 'head_rows': len(H), 'base_identities': len(axb), 'head_identities': len(axh),
    'duplicate_rows_base': sum(c - 1 for c in cb.values() if c > 1), 'duplicate_rows_head': sum(c - 1 for c in ch.values() if c > 1),
    'only_base': [{'module': m, 'name': n, 'axioms': list(axb[(m, n)]), 'moved_to': sorted(nh.get(n, []))} for m, n in only_b],
    'only_head': [{'module': m, 'name': n, 'axioms': list(axh[(m, n)]), 'moved_from': sorted(nb.get(n, []))} for m, n in only_h],
    'moved_names': [{'name': n, 'from': sorted(nb[n]), 'to': sorted(nh[n])} for n in moved],
    'axioms_changed': [{'module': m, 'name': n, 'base': list(axb[(m, n)]), 'head': list(axh[(m, n)])} for m, n in changed],
    'sorryAx_base': sorted(f'{m}:{n}' for (m, n), a in axb.items() if 'sorryAx' in a),
    'sorryAx_head': sorted(f'{m}:{n}' for (m, n), a in axh.items() if 'sorryAx' in a),
    'histogram_base': {', '.join(k) or '(none)': v for k, v in collections.Counter(axb.values()).most_common()},
    'histogram_head': {', '.join(k) or '(none)': v for k, v in collections.Counter(axh.values()).most_common()},
}
json.dump(res, open(sys.argv[3], 'w'), indent=1)
print(json.dumps({k: (v if not isinstance(v, list) else len(v)) for k, v in res.items() if not k.startswith('histogram')}))
