#!/usr/bin/env python3
"""Aggregate `#print axioms` comparison of two Checks logs (multi-line prints joined).
Usage: axcmp.py <base.log> <head.log> <out.json>. Records keep multiplicity; reports record
count, distinct-name count, dependency-bearing records, sorryAx records, and the multiset diff."""
import re, sys, json
from collections import Counter
def recs(path):
    t = open(path).read()
    out = []
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", t):
        out.append((m.group(1), tuple(sorted(a.strip() for a in m.group(2).replace('\n', ' ').split(',') if a.strip()))))
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", t):
        out.append((m.group(1), ()))
    return out
b, h = recs(sys.argv[1]), recs(sys.argv[2])
def summ(r):
    return {'records': len(r), 'distinct_names': len({n for n, _ in r}),
            'dependency_bearing_records': sum(1 for _, a in r if a),
            'dependency_bearing_distinct': len({n for n, a in r if a}),
            'sorryAx_records': sorted(n for n, a in r if 'sorryAx' in a),
            'axiom_sets': {', '.join(k) or '(none)': v for k, v in Counter(a for _, a in r).items()}}
cb, ch = Counter(b), Counter(h)
res = {'base': summ(b), 'head': summ(h), 'multisets_equal': cb == ch,
       'only_in_base': [f'{n}: {list(a)} x{c}' for (n, a), c in (cb - ch).items()],
       'only_in_head': [f'{n}: {list(a)} x{c}' for (n, a), c in (ch - cb).items()]}
json.dump(res, open(sys.argv[3], 'w'), indent=1)
print(json.dumps({k: (v if k not in ('base', 'head') else {kk: vv for kk, vv in v.items() if kk != 'axiom_sets'}) for k, v in res.items()}, indent=1))
