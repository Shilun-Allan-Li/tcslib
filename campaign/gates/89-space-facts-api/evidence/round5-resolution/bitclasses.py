"""Gate 89 round 5's resolution: classify every group of the binary-length sweep (round 5's
classifier, with the short-name keys of `OTHER` made file-qualified where a name recurs, after
round 5's finding 3, and the BL-1 members of findings 1 and 2 classified).
Usage: python3 -I bitclasses.py <bitsweep.tsv> <out.md>
The classes of the non-citation groups are assigned by hand below, from bitsweep-context.txt; a
group whose every hit is prose (backticks or a list item) is a docstring line; one whose every
hit cites a canonical lemma is a citation. An unassigned group stops the script."""
import sys, re, collections
rows = [l.rstrip('\n').split('\t') for l in open(sys.argv[1]).readlines()[1:] if l.strip()]
g = collections.OrderedDict()
for loc, d, txt in rows:
    f, n = loc.rsplit(':', 1)
    g.setdefault((f.replace('TCSlib/Complexity/', '').replace('TCSlib/', ''), d), []).append((int(n), txt))
BY = {  # (file suffix, declaration) -> class
 ('Machines/Bin.lean', 'length_bits_le'): 'H', ('Machines/Bin.lean', 'length_bits_mono'): 'H', ('Machines/Bin.lean', 'length_bits_le_log'): 'H',
 ('Machines/Bin.lean', 'two_pow_bits_le'): 'H', ('Encoding.lean', 'length_bits_le_self'): 'H', ('SpaceComplexity/Basic.lean', 'logSpace_le_size_succ'): 'H2',
 ('Build/CfgRecord.lean', 'record_pos_lt'): 'R4p', ('Randomized/SpaceAmplifyPoly.lean', 'lt_two_pow_bits'): 'R4p',
 ('CircuitComplexity/Meyer.lean', 'lenAll_inst'): 'R1c', ('CircuitComplexity/MeyerTableau.lean', 'bits_pad'): 'R1c',
 ('NTimeDiagonalizer.lean', 'qy_ones_ge'): 'R4e', ('NTimeDiagonalizer.lean', 'qy_two_pow_bits_le'): 'L3R5e', ('NTimeDiagonalizer.lean', 'qy_log_bits'): 'L3',
 ('NTimeDiagonalizer.lean', 'qy_call_bound'): 'R3e', ('NTimeDiagonalizer.lean', 'qy_bits_len_mono'): 'R2e', ('NTimeDiagonalizer.lean', 'qy_lt_two_pow_bits'): 'R4e',
 ('QuasiPolyHierarchy.lean', 'length_bits_eq'): 'L3', ('Constructible.lean', 'b3a_bits_length'): 'L3',
 ('Build/RecordTable.lean', 'rt_exists_boundTM'): 'R2l', ('Build/InputLength.lean', 'inputLength_count'): 'R2l', ('Build/Catalog.lean', 'f2_counter_count_space'): 'R2l',
 ('Logspace/Mult.lean', 'mult_product_length'): 'R4n',
 ('Randomized/BPLInP.lean', 'two_pow_codes_le'): 'C', ('Randomized/BPLInP.lean', 'BPL_subset_P'): 'C', ('Randomized/RandomWalkPad.lean', 'padDegree_le'): 'C',
 ('SpaceComplexity/Constructible.lean', 'b3a_log_machine'): 'C', ('Logspace/ISCountGenCorrect.lean', 'size_le_logSpace'): 'C', ('Logspace/ISCountGenCorrect.lean', 'compl_mem_NSPACE'): 'C',
 ('Randomized/SpaceAmplifyPoly.lean', 'logSpace_le_ell'): 'C', ('SpaceComplexity/Logspace/PathHard.lean', 'logSpace_le_ell'): 'O-strong',
 ('Randomized/UniformSample.lean', 'le_two_pow_size_pred'): 'R5k', ('Logspace/QueryReshape.lean', 'query_index_bound'): 'R5k',
}
OTHER = {'jacMeasure_step': 'O-size', 'jacobiAlg_eq': 'O-size', 'size_lt_of_two_mul_le': 'O-size', 'polyTimeComputable_gcd': 'O-size', 'le_padDegree': 'O-size',
 'lt_two_pow_size_succ': 'O-size', 'size_half': 'O-size', 'mul_two_pow_le_iff': 'O-size', 'emodRounds_le': 'O-size', 'size_eq_succ': 'O-size',
 'access_width_half': 'O-pos', 'cfgRecord_field_ne_nil': 'O-pos', 'rt_initRecord_fields': 'O-pos', 'exists_recordInitTM': 'O-pos', 'recordStep_width_one': 'O-pos',
 'f2_counter_heads': 'O-arith', 'uniformSampleAlg_pairEncode': 'O-arith', 'ell_eq_size': 'O-eq',
 'lupanov_arith': 'O-log', 'value_func': 'O-log', 'parityCircuit_depth_le': 'O-log', 'clog_poly_le': 'O-log', 'le_quasiPolyBudget': 'O-log', 'succ_pow_le_quasiPoly': 'O-log',
 'pow_add_one_le_pow_log': 'O-log', 'time_bound': 'O-log', 'count_bound': 'O-log', 'log2_meets': 'O-log', 'succ_le_two_pow_log': 'O-log'}
NAME = {'H': 'canonical home', 'H2': 'canonical home (LS-2)', 'C': 'citation', 'D': 'docstring', 'L3': 'LS-3 (ledgered)',
 'L3R5e': 'LS-3, and BL-1 (v) inline: E-D\'s file, which cannot reach `Machines/Bin` (ledgered)', 'R1c': 'BL-1 (i) residual: colleague-owned `CircuitComplexity`',
 'R2e': 'BL-1 (ii) residual: E-D\'s file, which cannot reach `Machines/Bin`', 'R3e': 'BL-1 (iii) residual: E-D in flight (its landing re-points it)', 'R4e': 'BL-1 (iv) residual: E-D\'s file, with no (iv) lemma it can reach',
 'R2l': 'BL-1 (ii) residual: `Machines/Bin` is above this layer', 'R4n': 'BL-1 (iv) residual: no (iv) lemma this file can reach',
 'R4p': 'BL-1 (iv): one of its two public statements', 'O-size': 'other: a `Nat.size` fact used natively, no bit length',
 'O-pos': 'other: positivity of a bit length', 'O-conv': 'other: the converse direction, no published lemma', 'O-arith': 'other: `Nat.size_eq_bits_len` as an arithmetic rewrite',
 'O-eq': 'other: a same-file definition\'s equation', 'R5k': 'BL-1 (v), inline: acknowledged by kind (gate 89 round 5, finding 1; 12.2c)', 'O-strong': 'other: a stronger bound', 'O-log': 'other: a `Nat.log` fact'}
CITE = re.compile(r'length_bits_le_self|length_bits_le_log|length_bits_le\b|length_bits_mono|length_bits_le_of_|length_bits_bitsVal_le|logSpace_le_size_succ|two_pow_bits_le|record_pos_lt|size_le_logSpace')
CODE = re.compile(r':=|exact|rw |rw\[|have |simpa|apply |refine|obtain')
out = ['| # | File · declaration | Lines | Class |', '|---|---|---|---|']; cnt = collections.Counter()
for i, ((f, d), hs) in enumerate(g.items(), 1):
    k = next((v for (ff, dd), v in BY.items() if f.endswith(ff) and d == dd), None) or OTHER.get(d)
    if k is not None and k in ('O-strong',) and not any(f.endswith(ff) and d == dd for (ff, dd) in BY): sys.exit(f'unqualified O-strong: {f} {d}')
    if k is None:
        texts = [t for _, t in hs]
        if all('`' in t or t.lstrip().startswith('*') for t in texts): k = 'D'
        elif all(CITE.search(t) for t in texts): k = 'C'
        else: sys.exit(f'unassigned: {f} {d} {texts}')
    cnt[k] += 1
    out.append(f'| {i} | `{f}` · `{d}` | {", ".join(str(n) for n, _ in hs)} | {NAME[k]} |')
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
print(len(g), 'groups:', ', '.join(f'{NAME[k]} {v}' for k, v in cnt.most_common()))
