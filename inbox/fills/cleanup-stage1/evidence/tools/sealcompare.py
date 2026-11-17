#!/usr/bin/env python3
"""sealcompare.py <base-rule10-dir> <head-rule10-dir> <targets.tsv> <out.md>   (cleanup-stage1)

Compares the canonical seals of every owner at the check base and the check head, per variant
(strict A, strict B, coe A, coe B): requests, errors (`^file:l:c: error[:(]` in the raw log), the
failing declarations (sealsum's attribution), the request rows added or removed (by spelling), and
whether any failure sits in a new declaration (targets.tsv).  A base failure set that reappears
identically at the head is attributed to the base.  Writes a Markdown table and a verdict.
"""
import json, os, re, sys

bd, hd, tsv, out = sys.argv[1:5]
new = {l.split('\t')[1] for l in open(tsv) if l.strip()}
VAR = [('strict A', 'seals/A', 'seals-A.tsv'), ('strict B', 'seals/B', 'seals-B.tsv'),
       ('coe A', 'seals-coe/A', 'seals-coe-A.tsv'), ('coe B', 'seals-coe/B', 'seals-coe-B.tsv')]


def load(d, sub, tsvname):
    recs = {}
    for f in os.listdir(os.path.join(d, sub)):
        if f.endswith('.json') and f != 'manifest.json':
            r = json.load(open(os.path.join(d, sub, f)))
            recs[r['module']] = r
    summ = {}
    for l in open(os.path.join(d, tsvname)):
        p = l.rstrip('\n').split('\t')
        summ[p[0]] = dict(requested=int(p[1]), rc=int(p[2]), errors=int(p[3]), install=p[4],
                          eof=p[5], decls=[x for x in p[6].split(',') if x])
    return recs, summ


lines = ['| Owner | Variant | Requests base → head | Rows added at head | Errors base → head | '
         'Failing declarations (head) | Same as base | In a new declaration |',
         '|---|---|---|---|---|---|---|---|']
bad = 0
for vname, sub, tsvname in VAR:
    brec, bsum = load(bd, sub, tsvname)
    hrec, hsum = load(hd, sub, tsvname)
    for mod in sorted(hrec):
        h = hrec[mod]; hs = hsum[h['label']]
        hrows = {r['spelling'] for r in h['rows']}
        if mod in brec:
            b = brec[mod]; bs = bsum[b['label']]
            brows = {r['spelling'] for r in b['rows']}
            reqs = f"{b['requested']} → {h['requested']}"
            added = sorted(hrows - brows); removed = sorted(brows - hrows)
            errs = f"{bs['errors']} → {hs['errors']}"
            same = sorted(bs['decls']) == sorted(hs['decls']) and bs['errors'] == hs['errors']
        else:
            reqs = f"new → {h['requested']}"; added = []; removed = []
            errs = f"new → {hs['errors']}"; same = hs['errors'] == 0
        innew = sorted(set(hs['decls']) & new)
        ok = same and not innew and not removed and hs['install'] == '1' and hs['eof'] == '1'
        bad += not ok
        lines.append(f"| `{mod}` | {vname} | {reqs} | {', '.join('`'+a+'`' for a in added) or '–'}"
                     f"{' (removed: ' + ', '.join(removed) + ')' if removed else ''} | {errs} | "
                     f"{', '.join('`'+d.split('.')[-1]+'`' for d in hs['decls']) or '–'} | "
                     f"{'yes' if same else 'NO'} | {', '.join(innew) or 'none'} |")
lines.append('')
lines.append(f'VERDICT: {"PASS" if not bad else "CHECK"}: {bad} row(s) differ from the base, carry a '
             'failure in a new declaration, lose a request row, or lack an install/EOF record.')
open(out, 'w').write('\n'.join(lines) + '\n')
print(lines[-1])
