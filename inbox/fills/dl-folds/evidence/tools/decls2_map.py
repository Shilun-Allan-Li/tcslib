#!/usr/bin/env python3
"""decls2_map.py DECLS2_TSV: re-check decls2's CHANGED rows modulo the textual name map of the
re-pointed readers and blocks (the short names a statement uses in source).

For each CHANGED row, the base header with every old short name replaced by its new short name
(word boundaries) is compared with the head header. Prints `SAME-MODULO-MAP` or `DIFFERENT` per row,
then the totals. A header differing only by re-pointed names is `SAME-MODULO-MAP`.
"""
import re, sys

TEXT_MAP = {
    'rdU': 'rU', 'rdZ': 'rZ', 'rdW': 'rW', 'rdState': 'rS', 'rdIdx': 'rI', 'rdQuery': 'rX',
    'rdLog': 'rL', 'rdAns': 'rAns', 'finU': 'rU', 'finZ': 'rZ', 'finW': 'rW', 'finL': 'rL',
    'finSt': 'rS', 'chunkAt': 'coinBlock',
}
if __name__ == "__main__":
    same = diff = 0
    for line in open(sys.argv[1]):
        p = line.rstrip('\n').split('\t')
        if p[0] != 'CHANGED':
            continue
        base, head = p[4], p[6]
        for o, n in TEXT_MAP.items():
            base = re.sub(r"(?<![\w.'])" + o + r"(?![\w'])", n, base)
        ok = base == head
        same += ok
        diff += not ok
        print(f"{'SAME-MODULO-MAP' if ok else 'DIFFERENT'}\t{p[2]}\t{p[1]}")
        if not ok:
            print(f"  base(mapped): {base}\n  head:         {head}")
    print(f"TOTAL CHANGED {same + diff}: SAME-MODULO-MAP {same}, DIFFERENT {diff}")
