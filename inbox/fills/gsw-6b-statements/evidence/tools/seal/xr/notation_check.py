r"""notation_check.py <collector-lines.log> <seal-outdir> <out.tsv> <name>... (gsw-6b-statements sub-agent `seal`, new).
Checks the "notation, never sealed" side of the seals made by seal_pipeline.sh: for each named constant (the brief's
reducible abbreviations, PolyExpr.eval, the FinDist coercion, ...) it prints its collector CAT row (kind, status,
abbrev, instance, home) and, for every seal record <seal-outdir>/seals-<V>/*.json, whether it is in the probe's
import closure and whether it is REQUESTED. Expected: no abbreviation/reducible constant is ever requested;
PolyExpr.eval is requested only in B and coe-B (SEAL_EVAL=1, its deliberate variant); FinDist.instCoeFunForallReal
is requested in A/B and not in coe-A/coe-B when it is in the closure (the coe variants' only change). Also lists,
per record, every requested constant that is an instance, and every requested constant whose collector status is
reducible and that is not a matcher (must be none; counted as unexpected)."""
import sys, json, glob, os
log, sd, out = sys.argv[1:4]; names = sys.argv[4:]
cat, clos = {}, {}
for l in open(log, encoding='utf-8'):
    if l.startswith('CAT '):
        r = json.loads(l[4:]); cat[r['name']['display']] = r
    elif l.startswith('CLOSURE '):
        r = json.loads(l[8:]); clos[r['module']] = set(r['closure'])
lines = ['# constant\tkind\tstatus\tabbrev\tinstance\thome']
for n in names:
    r = cat.get(n)
    lines.append('\t'.join([n] + ([r['kind'], r['status'], str(r['abbrev']), str(r['instance']), r['home']['display']] if r else ['NOT-IN-CATALOG'])))
lines.append('# variant\tprobe\trequests\t' + '\t'.join(names) + '\trequested_instances\trequested_reducible_nonmatcher')
bad = 0
for V in ('A', 'B', 'coeA', 'coeB'):
    for p in sorted(glob.glob(os.path.join(sd, f'seals-{V}', '*.json'))):
        if p.endswith('manifest.json'): continue
        r = json.load(open(p)); req = {x['spelling'] for x in r['rows']}
        cells = []
        for n in names:
            c = cat.get(n)
            if c is None: cells.append('-'); continue
            inclo = c['home']['display'] in clos[r['module']]
            st = ('REQUESTED' if n in req else 'not-requested') if inclo else ('own-file' if c['home']['display'] == r['module'] else 'outside-closure')
            want_req = ((n == 'Complexity.PolyExpr.eval' and V in ('B', 'coeB')) or
                        (n == 'TCSlib.InformationTheory.FinDist.instCoeFunForallReal' and V in ('A', 'B')))
            if inclo and (n in req) != want_req: bad += 1; st += '(UNEXPECTED)'
            cells.append(st)
        inst = sorted(x['spelling'] for x in r['rows'] if x['instance'])
        red = sorted(x['spelling'] for x in r['rows'] if x['collector_reducibility'] == 'reducible' and not x['matcher'])
        bad += len(red)
        lines.append('\t'.join([V, r['label'], str(r['requested'])] + cells + [','.join(inst) or '-', ','.join(red) or '-']))
lines.append(f'# RESULT unexpected={bad}')
open(out, 'w').write('\n'.join(lines) + '\n'); print('\n'.join(lines))
