"""Round-3 classification of a v3 screen's pairs (one tree), carried from round 2.

Pairs with a round-2 id keep round 2's class, family and group (audits/evidence/arm-fill/r2/
classify.tsv, acknowledged by the user), with these round-3 changes (each from a round-2 finding
or a user decision, named in the basis column):
  R2-1  L066 (`arm_reach` ~ `DblLang.Rch.trans`): N -> G, K18, A2a; OPEN, acknowledged debt
        (user: waits for Hydroxyi's guarded-run composition lemma, ARM-2 (a)).
        L049 (`halvCount_loop` ~ `InputAccess.access_width_half`): N -> G, family G-halfwidth, P1.
  R2-3  S072, S073, S074 (`PathHardRegs.orc_init/orc_acc/orc_step`): N -> G, K2, A2b.
  R2-4  I082, I083: G -> N, X (false positives: length-oracle facts, not `orc_bit`).
  user  L033 (G-rep, `pt_rep_mul`): P1+ -> A2w (ARM-2 and the user's dedup window, home decision).
        L119, L120 (G-vword): P1+ -> N, X (accepted as not real duplication).
Pairs new at this tree (ids N3-*): internal and same-file pairs by round 2's rule (S >= 200
shared; G when the larger directed share is >= 90% of a smaller body of >= 100 chars; else N);
library pairs from the inspected table <n3lib.tsv> (pid-independent key: copy path::name, source
path::name), which must cover every new library pair.
usage: python3 -I classify3.py <pairs3.tsv> <r2-classify.tsv> <r2-kfam.tsv> <n3lib.tsv> <out.tsv> [<tree-overrides.tsv>]
Tree overrides (pid, class, family, group, reason) apply to one tree only: at the landed tree, pairs the
payback re-pointed whose two sides now both cite the shared declaration."""
import sys
ptsv, r2c, r2k, n3lib, dst = sys.argv[1:6]
treeov = sys.argv[6] if len(sys.argv) > 6 else None  # tree-specific overrides (the landed tree's re-pointed pairs)
r2 = {c[0]: c for c in (l.rstrip('\n').split('\t') for l in open(r2c, encoding='utf-8')) if c[0] != 'pid'}
OV = {
 'L066': ('G', 'K18', 'A2a', 'R2-1: the complete guarded-run composition of DblLang.Rch.trans, inlined; OPEN, acknowledged debt (waits for Hydroxyi)'),
 'L049': ('G', 'G-halfwidth', 'P1', 'R2-1: re-proves InputAccess.access_width_half (promoted and cited by the payback)'),
 'S072': ('G', 'K2', 'A2b', 'R2-3: the preimage-oracle answer argument repeated (orc_init/orc_step)'),
 'S073': ('G', 'K2', 'A2b', 'R2-3: the preimage-oracle answer argument repeated (orc_acc/orc_init)'),
 'S074': ('G', 'K2', 'A2b', 'R2-3: the preimage-oracle answer argument repeated (orc_acc/orc_step)'),
 'I082': ('N', '-', 'X', 'R2-4: false positive (searchLang_mem_PSPACE proves a length-oracle fact, not orc_bit)'),
 'I083': ('N', '-', 'X', 'R2-4: false positive (NSPACE_poly_subset_PSPACE proves a length-oracle fact, not orc_bit)'),
 'L033': ('G', 'G-rep', 'A2w', 'user 2026-10-14: deferred to ARM-2 and the dedup window, with a home decision'),
 'L119': ('N', '-', 'X', 'user 2026-10-14: G-vword accepted as not real duplication'),
 'L120': ('N', '-', 'X', 'user 2026-10-14: G-vword accepted as not real duplication'),
}
TOV = {}
if treeov:
    for l in open(treeov, encoding='utf-8'):
        if l.startswith('#') or not l.strip(): continue
        pid, c, f, g, why = l.rstrip('\n').split('\t'); TOV[pid] = (c, f, g, why)
lib = {}
for l in open(n3lib, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    a, b, c, fam, grp, why = l.rstrip('\n').split('\t'); lib[(a, b)] = (c, fam, grp, why)
out = open(dst, 'w', encoding='utf-8'); out.write('pid\tcat\tclass\tfamily\tgroup\tbasis\n'); cnt = {}
for l in open(ptsv, encoding='utf-8'):
    c = l.rstrip('\n').split('\t')
    if c[0] == 'pid': continue
    pid, cat = c[0], c[1]
    if pid in TOV: cls, fam, grp, basis = TOV[pid]; basis = 'this tree: ' + basis
    elif pid in OV: cls, fam, grp, basis = OV[pid]
    elif pid in r2: _, _, cls, fam, grp, basis = r2[pid]; basis = 'round 2: ' + basis
    elif cat == 'lib':
        k = (f'{c[2]}::{c[3]}', f'{c[7]}::{c[8]}')
        if k not in lib: raise SystemExit(f'new library pair {pid} {k} has no inspected class')
        cls, fam, grp, basis = lib[k]; basis = 'round 3 (new pair, inspected): ' + basis
    else:
        sh = int(c[13]); mn = min(int(c[6]), int(c[11]))
        if sh >= 200: cls, basis = 'S', f'round 3 rule (new pair): {sh} shared >= 200'
        elif mn >= 100 and sh >= 0.9 * mn: cls, basis = 'G', f'round 3 rule (new pair): {sh}/{mn} of the smaller body'
        else: cls, basis = 'N', f'round 3 rule (new pair): {sh} shared'
        fam, grp = ('-', 'X') if cls == 'N' else ('new', 'A2b')
    cnt[(cat, cls, grp)] = cnt.get((cat, cls, grp), 0) + 1
    out.write(f'{pid}\t{cat}\t{cls}\t{fam}\t{grp}\t{basis}\n')
for k in sorted(cnt): print(k, cnt[k])
unused = [k for k in OV if k not in {l.split('\t')[0] for l in open(ptsv, encoding="utf-8")}]
print('round-3 changes not applicable at this tree (pair absent):', unused or 'none')
