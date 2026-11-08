#!/usr/bin/env python3
"""Compare two C3 tables (`C3\t<root module>\t<root>\t<eq theorem>\t<eq home>\t<parent>\t<parent home>`):
foreign generated-equation references from stored roots of owned modules (cleanup-part2).

python3 -I c3cmp.py <base c3.tsv> <head c3.tsv> <out.json>"""
import sys, json, collections
def load(p):
    rows = []
    for line in open(p):
        if line.startswith('C3\t'):
            rows.append(tuple(line.rstrip('\n').split('\t')[1:]))
    return rows
B, H = load(sys.argv[1]), load(sys.argv[2])
sb, sh = set(B), set(H)
res = {'base_pairs': len(B), 'head_pairs': len(H), 'base_unique': len(sb), 'head_unique': len(sh),
       'removed': [list(x) for x in sorted(sb - sh)], 'added': [list(x) for x in sorted(sh - sb)],
       'kept': [list(x) for x in sorted(sb & sh)],
       'head_by_root_module': dict(collections.Counter(x[0] for x in H).most_common())}
json.dump(res, open(sys.argv[3], 'w'), indent=1, ensure_ascii=False)
print(json.dumps({k: (v if not isinstance(v, (list, dict)) else len(v)) for k, v in res.items()}))
