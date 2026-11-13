#!/usr/bin/env python3
"""bodies_map.py BODIES_TSV: re-check bodies.py's CHANGED-BODY / CHANGED-PRIVATE-HEADER rows modulo
the textual name map of the re-pointed readers, blocks and their lemmas (decls2_map.py's map, plus
the private answer readers `rFwd`, `rY` and the projections of the deleted bundle lemmas)."""
import re, sys
sys.path.insert(0, '/workspace/foldtools')
from decls2_map import TEXT_MAP  # noqa: E402

EXTRA = [
    (r'polyTimeComputable_rd\.1\b', 'polyTimeComputable_rU'),
    (r'polyTimeComputable_rd\.2\.2\.2\.2\.2\.1\b', 'polyTimeComputable_rX'),
    (r'polyTimeComputable_rd\.2\.2\.2\.2\.2\.2\.2\b', 'polyTimeComputable_rAns'),
    (r'polyTimeComputable_finFields\.2\.2\.2\.1\b', 'polyTimeComputable_finA'),
]
WORDS = dict(TEXT_MAP, rFwd='rAns', rY='rAns')
rows = open(sys.argv[1]).read().split('\n')
same = diff = 0
i = 0
while i < len(rows):
    r = rows[i]
    if r.startswith('CHANGED'):
        base = rows[i + 1].split('base: ', 1)[1]
        head = rows[i + 2].split('head: ', 1)[1]
        for pat, rep in EXTRA:
            base = re.sub(pat, rep, base)
        for o, n in WORDS.items():
            base = re.sub(r"(?<![\w.'])" + o + r"(?![\w'])", n, base)
        ok = base == head
        same += ok
        diff += not ok
        print(f"{'SAME-MODULO-MAP' if ok else 'DIFFERENT'}\t{r}")
        if not ok:
            print(f"  base(mapped): {base}\n  head:         {head}")
        i += 3
        continue
    i += 1
print(f"TOTAL CHANGED {same + diff}: SAME-MODULO-MAP {same}, DIFFERENT {diff}")
