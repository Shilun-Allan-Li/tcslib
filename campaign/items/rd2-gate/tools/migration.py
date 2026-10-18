"""RD-2a migration list for TQBF.lean's B4a block (tip lines 114-1811), by declaration.
Categories (end state after RD-2a/RD-2b):
  KEEP     byte-identical
  KEEP-R   byte-identical up to the rename map (merged private -> public identifiers)
  MERGE    private definition deleted; its uses renamed to the identical public definition
  MOVE     generic; deleted here, its role taken by a FormulaKit declaration
  REWRITE  same role, new statement or proof over the closed form
  RETIRE   deleted, no successor
Reference analysis: a declaration proposed KEEP whose text names a non-KEEP declaration is
reported (KEEP-R if every such name is in the rename map, otherwise a conflict)."""
import re, sys, collections
path = sys.argv[1]
lines = open(path, encoding='utf-8').read().split('\n')
kw = re.compile(r'^(?:private\s+)?(?:noncomputable\s+)?(def|theorem|lemma|abbrev|structure|inductive)\s+(\S+)')
heads = [(i + 1, kw.match(l).group(2)) for i, l in enumerate(lines) if kw.match(l)]
rng = {}
for k, (ln, name) in enumerate(heads):
    s = ln
    if lines[ln - 2].rstrip().endswith('-/'):
        b = ln - 1
        while not lines[b - 1].lstrip().startswith('/--'): b -= 1
        s = b
    rng[name] = [s, None, ln]
names = [n for _, n in heads]
for k, n in enumerate(names):
    nxt = rng[names[k + 1]][0] - 1 if k + 1 < len(names) else len(lines)
    e = nxt
    while e > rng[n][2] and (lines[e - 1].strip() == '' or lines[e - 1].startswith('/-! ')
                             or lines[e - 1].startswith('-/') and False):
        e -= 1
    rng[n][1] = e
block = [n for n in names if 114 <= rng[n][2] <= 1811]

MERGE = {'codecSummaryWord': 'ConfigCodec.summaryWord', 'CodecCase': 'ConfigCodec.Case',
         'codecAction': 'ConfigCodec.caseAction', 'codecReadSymbol': 'ConfigCodec.readSymbol',
         'codecReadSummary': 'ConfigCodec.readSummary', 'CodecPort': 'ConfigCodec.Port (at M.k)',
         'codecCnfCost': 'FormulaKit.cost', 'codecCnfCost_relabel': 'FormulaKit.cost_relabel',
         'codecCnfCost_append': 'FormulaKit.cost_append',
         'codecCnfCost_flatMap_le': 'FormulaKit.cost_flatMap_le'}
MOVE = {'codecOneHot': 'FormulaKit.exactlyOne', 'codecOneHot_eval': 'FormulaKit.exactlyOne_eval',
        'codecOneHot_cost': 'FormulaKit.exactlyOne_cost_le',
        'codecCnf_numVars': 'FormulaKit.numVars_le_of_forall_lt',
        'codecCnf_serialize': 'FormulaKit.serialize_length_le',
        'codecLocalCheck': 'FormulaKit.gate, FormulaKit.gate_cost_le',
        'codecPort_card': 'ConfigCodec.card_port'}
SEEDS = {'codecWord', 'configurationCodec', 'codecValidity', 'configurationValidity',
         'configurationAcceptance', 'codecPairWire', 'configurationInputEquality',
         'codecTransitionCNF', 'configurationAdjacency'}
SUCC = {
 'codecWord': 'ConfigCodec.code', 'codecWord_length': 'ConfigCodec.code_length',
 'codecWord_get': 'ConfigCodec.code_getD_*', 'codecWord_eq_iff': 'ConfigCodec.code_eq_iff',
 'configurationCodec': 'ConfigCodec.code', 'configurationCodec_length': 'ConfigCodec.code_length',
 'configurationCodec_input_eq': 'ConfigCodec.code_input_eq',
 'configurationCodec_eq_iff': 'ConfigCodec.code_eq_iff',
 'codecValidity': 'ConfigCodec.validity', 'codecValidity_eval': 'ConfigCodec.validity_eval_iff',
 'configurationValidity': 'ConfigCodec.validity',
 'configurationValidity_eval': 'ConfigCodec.validity_eval_iff',
 'configurationAcceptance': 'ConfigCodec.acceptance',
 'configurationAcceptance_eval': 'ConfigCodec.acceptance_eval_iff',
 'codecValidity_cost_raw': 'validity cost ledger (same count, over FormulaKit.cost)',
 'codecValidity_cost': 'validity cost ledger',
 'configurationValidity_literals': 'ConfigCodec.validity_numVars_le',
 'configurationValidity_numVars': 'ConfigCodec.validity_numVars_le',
 'configurationValidity_size_raw': 'ConfigCodec.exists_serialize_length_le',
 'configurationAcceptance_bounds': 'ConfigCodec.acceptance_numVars_le',
 'configurationValidity_size': 'ConfigCodec.exists_serialize_length_le',
 'configurationAcceptance_size': 'ConfigCodec.exists_serialize_length_le',
 'codecPairWire': 'closed-form pair reads of code ++ code', 'codecPairWire_lt': 'closed-form pair reads',
 'configurationCodec_pair_get': 'closed-form pair reads',
 'configurationInputEquality': 'ConfigCodec.inputEquality',
 'configurationInputEquality_reject': 'ConfigCodec.adjacency_eval_of_ne',
 'configurationInputEquality_bounds': 'adjacency ledger',
 'configurationCodec_step_congr': 'corollary of ConfigCodec.code_eq_iff, if still needed',
 'codecTransitionCNF': 'ConfigCodec.transition',
 'codecTransitionCNF_eval': 'gate bridge and coverage of the closed-form enumeration',
 'codecTransitionCNF_step_iff': 'restated over the gate conjunction; proof body from its second line',
 'codecTransitionCNF_cost': 'adjacency ledger', 'configurationAdjacency': 'ConfigCodec.adjacency',
 'configurationAdjacency_eval': 'ConfigCodec.adjacency_eval_iff',
 'configurationAdjacency_reject': 'ConfigCodec.adjacency_eval_of_ne',
 'codecTransitionCNF_cost_poly': 'adjacency ledger',
 'codecAdjacency_cost': 'adjacency ledger', 'configurationAdjacency_bounds': 'adjacency ledger'}
RETIRE = {'codecWord_padding', 'codecWord_reconstruct', 'codecPadding', 'codecPadding_eval',
          'codecPadding_cost', 'codecGate_cnf', 'codecGateCNF', 'codecGateCNF_spec',
          'CodecGateIndex', 'exists_adjacency_codec_cnf'}
cat = {}
for n in block:
    cat[n] = ('MERGE' if n in MERGE else 'MOVE' if n in MOVE else 'REWRITE' if n in SEEDS
              else 'RETIRE' if n in RETIRE else 'KEEP')
text = {n: '\n'.join(lines[rng[n][0] - 1: rng[n][1]]) for n in block}
# reference analysis
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
refs = {n: {t for t in ident.findall(text[n]) if t in cat and t != n} for n in block}
bad = {'MOVE', 'REWRITE', 'RETIRE'}
changed = True
while changed:
    changed = False
    for n in block:
        if cat[n] not in ('KEEP', 'KEEP-R'): continue
        b = {r for r in refs[n] if cat[r].split(':')[0] in bad | {'CONFLICT'}}
        if b:
            cat[n] = 'REWRITE'; changed = True
        elif cat[n] == 'KEEP' and refs[n] & set(MERGE):
            cat[n] = 'KEEP-R'; changed = True
tot = collections.Counter()
for n in block:
    s, e, _ = rng[n]; ln = e - s + 1; c = cat[n].split(':')[0]
    tot[c] += ln
    succ = MERGE.get(n) or MOVE.get(n) or SUCC.get(n, '' if cat[n] != 'REWRITE' else '?')
    extra = cat[n][9:] if cat[n].startswith('CONFLICT') else ''
    print(f"| `{n}` | {s}–{e} | {ln} | {cat[n].split(':')[0]} | {succ}{extra} |")
print()
for c in ['KEEP', 'KEEP-R', 'MERGE', 'MOVE', 'REWRITE', 'RETIRE', 'CONFLICT']:
    print(c, tot[c], sum(1 for n in block if cat[n].split(':')[0] == c))
print('declarations', len(block), 'lines', sum(tot.values()))
