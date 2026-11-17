# eqrefs.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW, suite item 5 (generated-equation reads; #248 channel C3 and
# the historical eqn-term rows). From the collectors' ROOT eqn_refs (NmCollect.template.lean, dw10 addition 3): every
# stored constant of an owner whose type or value uses a foreign TCSlib definition's eq_<n>, eq_def, eq_unfold or splitter,
# attributed to its declaration (the stored constant's name without the private prefix and the auxiliary suffixes
# proof_N, match_N, eq_N, ...). A stored constant that is itself an equation lemma or splitter realized in the owner for a
# foreign definition (its base name is not a declaration of the owner) is listed with attributed=no (generated, not a read).
# Usage: python3 -I eqrefs.py <evidence> <out.tsv>
import sys, json, re, os, glob, collections
ev, outp = sys.argv[1:3]
AUX = re.compile(r'\.(proof_\d+|match_\d+|eq_\d+|eq_def|eq_unfold|_unary|_binary|_sunfold|_unsafe_rec|splitter|_proof_\d+|_simp_\d+|_cstage\d|_lambda_\d+|_eq_\d+)$')
def userbase(n):
    n = re.sub(r'^_private\.[^ ]*?\.0\.', '', n) if n.startswith('_private.') else n
    while AUX.search(n): n = AUX.sub('', n)
    return n
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(ev, 'collect/batches.tsv'))][1:]
mod2path = {r[1]: r[2] for r in rows}
out = []
for b in sorted({r[0] for r in rows}):
    lp = os.path.join(ev, 'collect', b, 'runs/mods', f'DW10Probe_Collect_{b}.log')
    if not os.path.exists(lp): continue
    names = collections.defaultdict(set); recs = []
    for l in open(lp, encoding='utf-8'):
        if l.startswith('ROOT '):
            r = json.loads(l[5:]); names[r['module']].add(userbase(r['name']['display'])); recs.append(r)
    for r in recs:
        for e in r.get('eqn_refs', []):
            base = userbase(r['name']['display'])
            attributed = 'yes' if base != userbase(e['target']['display']) else 'no'
            out.append([mod2path.get(r['module'], r['module']), base, r['name']['display'], e['ref']['display'], e['target']['display'],
                        e['target_home'], e['target_kind'], e['in'], attributed, b])
with open(outp, 'w') as f:
    f.write('path\tdeclaration\tstored_constant\tref\ttarget\ttarget_home\ttarget_kind\tin\tattributed\tbatch\n')
    for x in out: f.write('\t'.join(x) + '\n')
print('eqn refs', len(out), 'attributed', sum(1 for x in out if x[8] == 'yes'))
