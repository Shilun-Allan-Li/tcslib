from pathlib import Path
import csv, hashlib, io, json, re

B = Path('/private/tmp/io-sprg-proof-notes/M3Prepared')
O = Path('/private/tmp/io-sprg-proof-notes/M3TemplateAudit')
index = json.loads((B / 'overlap/probe-index.json').read_text())
helpers = {
 'bucket_count_upper': ('Params.B_eq; Params.W_pos', 'Exact max-one ceiling formula; W>0 is existing width positivity.'),
 'bucket_count_lower': ('Params.B_eq; Params.W_pos', 'Same exact max-one ceiling formula, multiplied by W.'),
 'prefactor_eventually_le_two_pow': ('bucket_count_upper; BoolPRG.outLen_le; Params.m_eq/n_eq/ℓ_eq; PolyExpr.eval_subst', 'q is the actual outBound composed with the polynomial input schedule; hm/hB are prior public conclusions, not the final goal.'),
 'cond1_single_le_quarter': ('Params.cond1_prob_le; Params.Γ_eq; Params.W_pos', 'Strict Markov denominator Γ+1 retained; hlog is the actual explicit logarithmic cutoff.'),
 'cond1_repetitions_fixed_index': ('cond1_single_le_quarter; Draw reader; uprob_pi_forall; uprob_fst', 'Noise predicate is fixed after fixing the entire actual index; h is the preceding scalar bound, not the tuple conclusion.'),
 'cond1_all_fixed_index': ('cond1_repetitions_fixed_index; Params.sdSampFull_eq; Params.sdCore_draw; Params.draw_eq', 'h is the preceding repetition result; conclusion adds only the actual independent Boolean seed product.'),
 'cond1_all_joint': ('cond1_all_fixed_index; Params.jointLaw_eq; prob_bind/expect_map/expect_mono/expect_const', 'idx is the actual possibly nonuniform idSamp law; section bound is the preceding fixed-index theorem.'),
 'binomial_ratio_quarter': ('Internal.binomial_bound; power monotonicity', 'hbase is the required denominator/base inequality and κ≤r; neither premise assumes the final choose-tail bound.'),
 'smallset_bucket_tail_quarter': ('Internal.some_bucket_tail; binomial_ratio_quarter; Params.t_eq', 'Literal finite bucket fiber and S retained; S.card≤Γ≤B matches the actual sparse event.'),
 'capacity_bucket_tail_quarter': ('Internal.some_full_bucket_tail; binomial_ratio_quarter; bucket_count_lower; Params.cap_eq/rc_eq/W_eq', 'κ²*W is exact capacity; hround is prior rounding bound, not a tail estimate.'),
 'cond3_joint_le_quarter_pow': ('capacity_bucket_tail_quarter; Params.jointLaw_eq/idSamp_eq/sdSampFull_eq/idCore_eq; overfull_iff', 'G is actual generator DRAW, not G.Idx. Uniform bucket marginal is extracted from the actual draw product.'),
 'cond2_sparse_joint_le_quarter_pow': ('smallset_bucket_tail_quarter; badSet_eq; cond1_iff/cond2_iff; actual joint-law bridge; bucket-last product equivalence', 'S depends on generator DRAW, matrix and full seed draw, not bucket labels; smallness remains inside the event.')
}
originals = {
 'errProb_nonneg': ('Params.errProb_eq; ProbComp.prob_nonneg', 'Abstract computation and actual err flag; no support/independence assumption.'),
 'badSet_expect_le': ('Params.badSet_eq/errSet_eq/noiseValue_eq; lpnNoise_sample; hasLocality_iff', 'Actual vars and literal selector/residue integer-lift noise are expanded; actual uniform vector law retained.'),
 'cond1_prob_le': ('badSet_expect_le; Γ integer threshold; public Lamport Markov bound', 'hmean is the preceding first-moment result; strict Γ<badCount becomes Γ+1, avoiding Γ=0 division.'),
 'errProb_le_decomposition': ('jointLaw_eq/idSamp_eq/sdSampFull_eq; firstGood_none_iff; oneSd_flag/oneFlag_eq; cond1_iff/cond2_iff/cond3_iff', 'Actual uniform input product X after exact-law transport; hflags is the flag reader, not a probability assumption.'),
 'claim42': ('errProb_le_decomposition; cond3/cond2/cond1 joint helpers; prefactor_eventually_le_two_pow', 'hparts is the actual earlier decomposition and three component bounds; both cutoffs precede every pp. No PP-dependent cutoff.')
}
expected = {n + '_core' for n in helpers} | {n + '_core' for n in originals}
regular = (B / 'overlap/names.txt').read_text().splitlines()
controls = (B / 'overlap/control-names.txt').read_text().splitlines()
assert len(index) == 23 and len(regular) == 22 and controls == ['cond2_hunif_control']
assert set(regular) | set(controls) == {r['name'] for r in index}
assert expected <= set(regular)
assert len([r for r in index if r['family'] == 'M3-helper-core']) == 12
assert len([r for r in index if r['family'] == 'M3-frozen-original-core']) == 5
issues = []
rows = []
for row in index:
    p = B / 'overlap' / row['template']
    text = p.read_text()
    imports = re.findall(r'^import (\S+)', text, re.MULTILINE)
    if imports != row['imports']:
        issues.append({'name': row['name'], 'issue': 'import index mismatch'})
    if any('StructuredSeed' in m for m in imports):
        issues.append({'name': row['name'], 'issue': 'owned import'})
    assert text.count('__PROBE_BODY__') == 1
    assert not re.search(r'\b(sorry|admit)\b', text)
    if row['name'] in expected:
        stem = row['name'].removesuffix('_core')
        deps, abstraction = (helpers | originals)[stem]
        fullname = ('Internal.' if stem in helpers else 'Params.') + stem
    elif row['name'] == 'cond2_hunif_control':
        fullname = 'Control only: Bridge.prob_sample_pair + prob_sample_eq_uprob'
        deps = 'Existing public uniform pair probability bridge'
        abstraction = 'Type0 exact semantic law bridge; not a new helper or original obligation.'
    else:
        fullname = 'Internal.' + row['name']
        deps = 'Frozen Load lemma with Buckets.bucket/load replaced by the finite fiber filter'
        abstraction = 'Original thresholds, finite sample type and positivity hypotheses preserved.'
    rows.append({'probe':row['name'],'family':row['family'],'actual_declaration':fullname,
                 'public_reader_or_prior_dependencies':deps,
                 'abstraction_justification':abstraction,
                 'owned_imports':'NONE','exact_self_goal_assumption':'NONE_IDENTIFIED',
                 'template_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
                 'status':'STATIC_AUDIT_ONLY_SEARCH_NOT_RUN'})
assert not issues, issues
stream = io.StringIO();writer = csv.DictWriter(stream, fieldnames=list(rows[0]), delimiter='\t', lineterminator='\n')
writer.writeheader();writer.writerows(rows)
(O / 'core-to-source-map.tsv').write_text(stream.getvalue())
(O / 'summary.json').write_text(json.dumps({
 'status':'STATIC_COVERAGE_AND_FIDELITY_AUDIT_PASS_NO_LEAN',
 'index_entries':23,'regular_names':22,'public_reuse_controls':1,
 'new_helpers':12,'frozen_nonLoad_originals':5,'frozen_Load_originals':5,
 'missing_templates':[],'index_import_mismatches':[],
 'owned_imports':[],'exact_self_goal_assumptions_identified':[],
 'vacuous_mathematical_cores_identified':[],
 'new_or_modified_templates':[],
 'qualification':'Static text/semantic mapping only; no elaboration or exact?/apply? run. No global search absence claim.',
 'index_sha256':hashlib.sha256((B / 'overlap/probe-index.json').read_bytes()).hexdigest(),
 'names_sha256':hashlib.sha256((B / 'overlap/names.txt').read_bytes()).hexdigest(),
 'template_bindings':rows},indent=2)+'\n')
print('23 templates mapped: 12 new helpers + 5 original nonLoad + 5 Load + 1 public bridge control; no missing template')
