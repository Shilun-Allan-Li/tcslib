#!/usr/bin/env python3
"""Compare final and base results.

seals:  cmp_scans.py seals <final.jsonl> <base.jsonl>
        per file: final status/errors/declarations vs base; declarations failing at the final
        but not at the base are listed as NEW.
rwids:  cmp_scans.py rwids <final.tsv> <base.tsv>
        per file: explicit unfolds of foreign TCSlib definitions at the final and at the base;
        rows present at the final but not at the base are NEW."""
import sys, json, collections

def key(f):
    return f.replace('TCSlib/Cryptography/', '').replace('.lean', '').replace('/', '_')

mode = sys.argv[1]
if mode == 'seals':
    def load(p):
        d = {}
        for l in open(p):
            r = json.loads(l)
            d[key(r['file'])] = r
        return d
    F, B = load(sys.argv[2]), load(sys.argv[3])
    newtot = 0
    for k in sorted(F):
        f = F[k]
        b = B.get(k)
        fd = set(f['error_decls'])
        bd = set(b['error_decls']) if b else None
        new = sorted(fd - bd) if bd is not None else sorted(fd)
        newtot += len(new) if b else 0
        bs = f"base {b['status']}/{b['errors']} {sorted(bd)}" if b else 'base: new file'
        print(f"{k}: final {f['status']}/{f['errors']} {sorted(fd)} | {bs} | NEW {new}")
    print('NEW failing declarations (files existing at the base):', newtot)
else:
    def load(p):
        d = collections.defaultdict(set)
        for l in open(p):
            parts = l.rstrip('\n').split('\t')
            if len(parts) != 5:
                continue
            mod, ident, const, tag, home = parts
            if tag == 'FOREIGN-TCSLIB-DEF':
                d[mod].add((ident, const, home))
        return d
    F, B = load(sys.argv[2]), load(sys.argv[3])
    tot = 0
    for k in sorted(set(F) | set(B)):
        new = sorted(F[k] - B[k])
        tot += len(new)
        print(f"{k}: final {len(F[k])} foreign-def unfolds, base {len(B[k])}; NEW {new}")
        for r in sorted(F[k]):
            print(f"    final: {r}")
    print('NEW foreign explicit unfolds:', tot)
