"""Round-2 classification of every screen pair touching an added file (pack author's
classification, for the user's acknowledgement; the auditor is asked to challenge it).

Classes
  lib pairs (added <-> library):  D  disclosed family (D1-D7, by the disclosure table)
                                  U  undisclosed substantive copy (the twelve)
                                  G  small genuine helper duplication
                                  N  incidental (conventional fragment)
  internal and same-file pairs:   S  substantive: >= 200 shared characters of one specific
                                     argument or definition (not a tactic idiom)
                                  G  small genuine: near-identical restatement (the larger
                                     directed share >= 90% of the smaller body, smaller body
                                     >= 100 chars), or the same statement/definition restated
                                     in another file (named override)
                                  N  incidental: everything else (sibling lemmas sharing an
                                     idiom, closure or instantiation plumbing, span artifacts)
Rule first, then the named overrides below (each with its reason). Library pairs are classified
per copy-side declaration by inspection (no rule).
usage: python3 -I classify.py <pairs.tsv> <disclosed.tsv> <out.tsv> <kfam.tsv>"""
import sys
ptsv, disc, dst = sys.argv[1:4]
fams = {}
for l in open(disc, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    f, a, b = l.rstrip('\n').split('\t'); fams[frozenset([a, b])] = f.split()[0]
# ---- library: per copy-side declaration (added side = A) ----
U = {'arm_decides_space': 'U-bank', 'marm_dtime': 'U-bank', 'narm_decides': 'U-bank',
     'npre_of_npreS': 'U-bank', 'narm_decides_space': 'U-bank', 'narm_decides_poly': 'U-bank',
     'decChain': 'U-chain', 'runFrom_count_eq': 'U-count', 'spaceUsedWith_le_of_ranges': 'U-ranges',
     'MReach.trans': 'U-reach', 'MReach.halt': 'U-reach', 'length_lbStep': 'U-lbstep'}
LG = {'orc_bit': 'G-oracle', 'orc_len': 'G-oracle', 'MHalt.mono': 'G-reachkit',
      'vword_whole₂': 'G-vword', 'vword_whole₃': 'G-vword', 'foldr_max_le': 'G-foldr',
      'outSummary_eq_empty_iff': 'G-outsum', 'canon_of_getLastD': 'G-canon',
      'getLastD_of_canon': 'G-canon', 'pe_getD_snd': 'G-pairidx', 'getD_flatten_block': 'G-flatten',
      'prefixTruth_congr_agree': 'G-prefix', 'toCNF_extension_iff': 'G-tseitin',
      'pt_rep_mul': 'G-rep', 'eq_bits_append_replicate': 'G-bits'}
LN = {'lbStep_iterate', 'polyTimeComputable_levelBits', 'prefixTruth_imp_const',
      'prefixTruth_and_const', 'pt_take', 'pt_drop', 'pt_vwid', 'pt_orB', 'halvCount_loop',
      'slide_ok_iff', 'cellOf_congr', 'mrunFrom_eq', 'mcompileTM_init', 'marm_run', 'last_tape_run',
      'ndtm_runWith_eq_runFrom', 'arm_reach', 'rawEdge_adjWordE'}
# pair-level library exceptions: a pair of a non-incidental declaration whose own shared text
# is only a fragment or idiom
LIB_PAIR_N = {
 'L007': 'truthAux_nil (D6) vs QBF.truthAux_iff_prefixTruth: shared induction prelude only',
 'L008': 'truthAux_nil (D6) vs QBF.prefixTruth_congr: shared induction prelude only',
 'L061': 'inWin_of_coreSum_eq (D5, below-floor disclosed copy) vs codecObserve_congr: coreSum simp idiom',
 'L062': 'inWin_of_coreSum_eq (D5) vs s1b_record_eq_iff: coreSum simp idiom',
 'L074': 'MReach.trans vs Call.runFrom_forall_append: 80-char run_add fragment',
 'L082': 'MReach.halt vs Call.runFrom_forall_append: 80-char run_add fragment',
 'L051': 'pe_getD_snd vs Mult.mult_run: index rewrite inside a long run proof',
 'L053': 'pe_getD_snd vs Parse.jeqPlain_run: index rewrite inside a long run proof',
}
# ---- internal / same-file overrides ----
OV = {
 # to N despite >= 200 shared
 'S017': ('N', 'polynomial-time closure plumbing (pt_vlen/pt_vwid_lin), no shared argument'),
 'S047': ('N', 'two instantiations of the same existing generic scan lemma; shared text is its argument plumbing'),
 'I020': ('N', 'per-machine PreS discharge by cases over the label type (fin_cases/simp idiom)'),
 'I080': ('N', 'per-machine PreS discharge by cases over the label type (fin_cases/simp idiom)'),
 'I072': ('N', 'chains of per-instruction NSem step idioms'),
 'I073': ('N', 'chains of per-instruction NSem step idioms'),
 'I074': ('N', 'chains of per-instruction NSem step idioms'),
 # to G: the same statement or definition restated in another file
 'I009': ('G', 'orc_len restated per machine (input-length oracle answer)'),
 'I010': ('G', 'the input-length oracle fact re-proved inline (gen_start)'),
 'I011': ('G', 'orc_len restated per machine'),
 'I012': ('G', 'the input-length oracle fact re-proved inline (searchLang_mem_PSPACE)'),
 'I013': ('G', 'the input-length oracle fact re-proved inline (NSPACE_poly_subset_PSPACE)'),
 'I042': ('G', 'orc_len restated per machine (ExpBFS orcN_len)'),
 'I043': ('G', 'orc_len restated per machine (PathHardRegs)'),
 'I056': ('G', 'orc_len restated per machine (orcN_len / PathHardRegs)'),
 'I057': ('G', 'the input-length oracle fact re-proved inline (searchLang_mem_PSPACE)'),
 'I071': ('G', 'the input-length oracle fact re-proved inline (gen_start)'),
 'I082': ('G', 'the input-bit oracle fact re-proved inline (searchLang_mem_PSPACE)'),
 'I083': ('G', 'the input-bit oracle fact re-proved inline (NSPACE_poly_subset_PSPACE)'),
 'I084': ('G', 'the input-length oracle fact re-proved inline (searchLang_mem_PSPACE)'),
 'I085': ('G', 'the input-length oracle fact re-proved inline (NSPACE_poly_subset_PSPACE)'),
 'I016': ('G', 'identical instruction block mvI (body under 100 chars)'),
 'I017': ('G', 'identical instruction block dmI (body under 100 chars)'),
 'I023': ('G', 'dm_run: the run lemma of the identical dmI block, restated per machine'),
 'I081': ('G', 'sh_run: the run lemma of the identical shI block, restated per machine'),
 'I064': ('G', 'the code-step relation restated (SavitchARM.Rel, ExpBFS stp; cf. Codec.StepRel)'),
}
# ---- groups (user, 2026-10-14; backlog ARM-1 dedup decisions and ARM-2, at e831b5b0) ----
#  P1  the payback PR after the B6 hosts (decided list)
#  P1+ rows this ledger proposes to add to the payback list (copies of campaign code, or with D4)
#  A2a ARM-2 (a): re-derivations of Hydroxyi's earlier library
#  A2b ARM-2 (b): duplication inside the new files
#  X   not real duplication (incidental)
GRP_U = {'U-chain': 'P1', 'U-lbstep': 'P1', 'U-ranges': 'A2a', 'U-count': 'A2a', 'U-reach': 'A2a'}
GRP_U_BANK_B = {'arm_decides_space', 'marm_dtime', 'npre_of_npreS', 'narm_decides_space'}
GRP_G = {'G-oracle': 'P1+', 'G-canon': 'P1+', 'G-pairidx': 'P1+', 'G-outsum': 'P1+', 'G-prefix': 'P1+',
         'G-rep': 'P1+', 'G-vword': 'P1+', 'G-tseitin': 'P1+',
         'G-reachkit': 'A2a', 'G-bits': 'A2a', 'G-foldr': 'A2a', 'G-flatten': 'A2a'}
KGRP = {'K21': 'P1', 'K18': 'A2a'}   # every other internal/same-file family: A2b
kmap = {}
for l in open(sys.argv[4], encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    ids, k = l.rstrip('\n').split('\t')
    for i in ids.split(): kmap[i] = k
rows = [l.rstrip('\n').split('\t') for l in open(ptsv, encoding='utf-8')]
hdr, rows = rows[0], rows[1:]
out = open(dst, 'w', encoding='utf-8')
out.write('pid\tcat\tclass\tfamily\tgroup\tbasis\n')
cnt = {}
for c in rows:
    pid, cat = c[0], c[1]
    A, B = f'{c[2]}::{c[3]}', f'{c[7]}::{c[8]}'
    sh = int(c[13]); ca, cb = int(c[6]), int(c[11]); mn = min(ca, cb)
    if cat == 'lib':
        name = c[3]; f = fams.get(frozenset([A, B]))
        if f: cls, fam, basis = 'D', f, 'disclosure table'
        elif pid in LIB_PAIR_N: cls, fam, basis = 'N', '-', LIB_PAIR_N[pid]
        elif name in U: cls, fam, basis = 'U', U[name], 'substantive undisclosed copy (inspection)'
        elif name in LG: cls, fam, basis = 'G', LG[name], 'small genuine helper duplication (inspection)'
        elif name in LN: cls, fam, basis = 'N', '-', 'conventional fragment (inspection)'
        elif name in {'truthAux_nil', 'inWin_of_coreSum_eq'}: cls, fam, basis = 'N', '-', 'idiom pair of a disclosed declaration'
        else: raise SystemExit(f'unclassified library pair {pid} {name}')
    else:
        if pid in OV: cls, basis = OV[pid][0], 'override: ' + OV[pid][1]
        elif sh >= 200: cls, basis = 'S', f'rule: {sh} shared >= 200'
        elif mn >= 100 and sh >= 0.9 * mn: cls, basis = 'G', f'rule: {sh}/{mn} = {sh/mn:.0%} of the smaller body'
        else: cls, basis = 'N', f'rule: {sh} shared, {sh/mn:.0%} of the smaller body'
        fam = kmap.get(pid, '-') if cls != 'N' else '-'
    if cls == 'N': grp = 'X'
    elif cls == 'D': grp = 'P1'
    elif cls == 'U': grp = 'A2b' if c[3] in GRP_U_BANK_B else ('A2a' if fam == 'U-bank' else GRP_U[fam])
    elif cat == 'lib': grp = GRP_G[fam]
    else: grp = KGRP.get(fam, 'A2b')
    cnt[(cat, cls, grp)] = cnt.get((cat, cls, grp), 0) + 1
    out.write(f'{pid}\t{cat}\t{cls}\t{fam}\t{grp}\t{basis}\n')
for k in sorted(cnt): print(k, cnt[k])
