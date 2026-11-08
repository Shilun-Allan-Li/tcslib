"""Bounded source review of all51 rows exposed by widening9 to21 files."""
from pathlib import Path
import collections, json

OUT=Path(__file__).resolve().parent
data=json.loads((OUT/'population-expansion-accounting.json').read_text())
index={r['label']:r for r in json.loads((OUT/'base-index.json').read_text())}
live='Finite.lean::runFrom_state_ne_none_of_le'
private_live={'Catalog.lean::f2_loop_live_prefix','SAT.lean::sat_live_prefix','Hardness.lean::clA5_live_prefix'}
linear={'PolyTimePairing.lean::polyTimeComputable_of_linear','Hardness.lean::clNative_linear'}
mapping={'PolyTimePairing.lean::PolyTimeComputable.pairMapSnd','Hardness.lean::clNative_map'}
updates={'CounterProg.lean::tapes_update','CounterProg.lean::heads_update','CounterProg.lean::apply_act'}
ones={'UnaryTape.lean::update_ones_succ','UnaryTape.lean::update_ones_pred'}
walks={'CounterProg.lean::print_walk','CounterProg.lean::back_walk'}
moves={'Configuration.lean::moveInputPos_pos_of_ne_right','Configuration.lean::moveInputPos_neg_of_ne_left','Configuration.lean::moveInputPos_rightBoundary'}
prefix={'PolyTimePrefix.lean::polyTimeComputable_takePrefixByLength','PolyTimePrefix.lean::polyTimeComputable_dropPrefixByLength'}
step_output={'Deterministic.lean::step','Deterministic.lean::outputSymbol'}
halting={'Deterministic.lean::ComputesInTimeAndSpace','Deterministic.lean::haltsAtStep'}
code={'Encoding.lean::exists_codeTM_spaceUsed','Encoding.lean::FinTM.toCodeTM_computesInTime_iff'}
run_bounds={'CounterProg.lean::run_regs_le','CounterProgRun.lean::run_pos_le'}
first_halt={'SAT.lean::sat_call_first_halt','Hardness.lean::clA5_call_first_halt'}

notes={
'B01':('Live-prefix public/private rederivation',6,
 'Material generic reuse/watch candidate. Inspected headers: all three private Bool contracts are instances of public runFrom_state_ne_none_of_le; Catalog body is identical156/156. SAT/Hardness differ in the config binder spelling. These source proofs are unchanged by this PR. No new debt approval or sealed consumer success is inferred.'),
'B02':('Linear-time to polynomial-time wrapper',2,
 'Material pre-existing public/private proof duplication. The new clNative_linear body is a direct call to polyTimeComputable_of_linear, below the screen threshold. Source-level re-point is retained separately from compiler deletion and actual head-screen measurements.'),
'B03':('Threaded-map polynomial witness',2,
 'Material pre-existing public/private witness arithmetic. Current clNative_map uses the public pairMapSnd contract with its published equation; it no longer repeats the old witness/majorization construction. No new public contract or debt waiver is inferred.'),
'B04':('Pointwise update projections and directive tails',4,
 'Small funext/update proof scaffold. Canonical declaration spans include trailing omit[Fintype Λ][DecidableEq Λ]in, which belongs to the next declaration; heads_update/tapes_update actual normalized proof portions are below60. Keep all raw75-character scores, but do not call the entire raw span an independent75-character proof or count the directive as copied mathematics. apply_act contains the related field argument.'),
'B05':('Unary interval update duals',2,
 'Existing same-home dual statements use identical82-character pointwise update/split_ifs arithmetic proof schemas. The assertions concern successor versus predecessor interval changes. This is a real shared schema under distinct statements, not newly introduced source and not a debt acknowledgement.'),
'B06':('Counter-program print/back walk phases',2,
 'Material existing shared induction/transition scaffold with different commands, endpoints, output and arithmetic direction. back_walk raw body also carries a trailing omit directive. Definitions/tables and both proof bodies are unchanged here. No claim of permanent acceptability or complete factoring follows.'),
'B07':('Short run-step or induction fragments across clients',4,
 'SAT.satRed_one is exactly two published run-equation rewrites(63chars). Its matches inside larger walk/visited proofs are those same public rewrites, not the entire surrounding theorem. The print_walk/clCmp_forward edge is a short induction/run-step fragment in distinct phase proofs. Bounded body inspection supports the scaffold classification; no global no-duplication claim.'),
'B08':('Input-position direction/boundary facts',6,
 'Existing same-home related boundary/direction proofs share Fin/index branch arithmetic. Their statements concern different positions or directions; all are unchanged. Raw directed similarities remain, without approving debt or pretending a new API was authored.'),
'B09':('Prefix take/drop API instantiations',2,
 'Two existing distinct public results instantiate one shared PrefixByLength program/goes_total proof at true or false. The computational theorem is already shared. The drop raw denominator also includes endComplexity after its proof; raw165/180 denominators are retained exactly.'),
'B10':('Run/output and halt/resource predicate terms',4,
 'Term/data candidates, not proof copies: step versus outputSymbol share transition lookup but return different objects; ComputesInTimeAndSpace versus haltsAtStep share run-state tests but define different specifications. All eligible term bodies are identical base/head. No new table/data implementation is introduced.'),
'B11':('Pair-diagonal phases and token emission',4,
 'Existing phase/configuration packaging scaffold, including a substantial double/copy overlap398/475, plus shorter separator/run rewrites in other machines. Transition cases, states, emitted words and phase lengths differ; all source is unchanged. Material phase sharing is retained as a watch, not dismissed or newly acknowledged.'),
'B12':('Finite/code machine transport proofs',1,
 'Existing bundled-machine elimination/relabel transport scaffold used for distinct time-iff versus existential space-preserving encoding results. The shared fragment does not identify the whole mathematical assertions. No consumer conversion or new equation is proved in this screen task.'),
'B13':('Register and input-position run bounds',2,
 'Existing induction-on-run scaffold for different numeric components. The register proof consumes a step_regs_le bound; position proof establishes a distinct one-step bound. Keep both overlaps without claiming a new generic theorem or accepting legacy debt.'),
'B14':('Published pairing/append compositions',2,
 'Existing public closure results share calls to the public linear pairConcat contract and pairEncode composition. Distinct functions/conclusions use an already shared construction, not newly copied executable machines. Source remains unchanged.'),
'B15':('Output-length and projection witness fragments',5,
 'Source inspection finds clients extracting a concrete machine/time witness and applying the existing output_length_le reader with that exact bound; surrounding computation/image statements and visible coefficients differ. The projection edge is a short pairFst/pairSnd witness fragment. This is bounded fragment classification, not proof that the larger legacy image recipe is factored; full Composition comparison is added in the final25 population.'),
'B16':('Generic input trajectory bound',1,
 'Material generic reuse/watch candidate: inspected Catalog Bool header is the instance of public Deterministic.timed_input_bound. Both derive one-step displacement then induct on time. Source is unchanged; a reader re-point is not elaborated by this no-Lean task.'),
'B17':('First halt with positive time',2,
 'Material related generic proof. SAT/Hardness private statements add0<u from a live-start premise to public exists_first_halt result; least halt time, cut and stabilized endpoint are shared. Statement-level decomposition is explicit; no typed/opaque consumer check was run and no new API gap or approval is inferred.')}

groups=collections.defaultdict(list)
for row in data['newly_exposed_baseline_rows']:
    a,b=row['a'],row['b']; pair={a,b}; matches=[]
    def add(cond,key):
        if cond:matches.append(key)
    add(live in pair and bool((pair-{live})&private_live),'B01')
    add(pair==linear,'B02');add(pair==mapping,'B03')
    add(pair<=updates,'B04');add(pair==ones,'B05');add(pair==walks,'B06')
    add((b=='SAT.lean::satRed_one' and a in walks|{'Deterministic.lean::visitedByTapeHead_step_subset'}) or
        (a=='CounterProg.lean::print_walk' and b=='Hardness.lean::clCmp_forward'),'B07')
    add(pair<=moves,'B08');add(pair==prefix,'B09')
    add(pair==step_output or pair==halting,'B10')
    add(a.startswith('Encoding.lean::pairDiag_') and b in {
        'Encoding.lean::pairDiag_copy','Hardness.lean::clCmp_forward','Primitives.lean::emitterToken_separator'},'B11')
    add(pair==code,'B12');add(pair==run_bounds,'B13')
    add(b=='PolyTimePairing.lean::PolyTimeComputable.append' and a in {
        'PolyTimePairing.lean::PolyTimeComputable.pairEncode','PolyTimePairing.lean::polyTimeComputable_pairConcat'},'B14')
    add(b=='PolyTime.lean::PolyTimeComputable.output_length_le' or
        (a=='PolyTimePairing.lean::PolyTimeComputable.pairEncode' and b=='SAT.lean::sat_pt_fields'),'B15')
    add(a=='Deterministic.lean::timed_input_bound' and b=='Catalog.lean::f2_loop_input_run_le','B16')
    add(a in first_halt and b=='Finite.lean::exists_first_halt','B17')
    assert len(matches)==1,(row,matches)
    groups[matches[0]].append(row)
assert sum(len(v) for v in groups.values())==51
result=[]
for key,(title,count,note) in notes.items():
    assert len(groups[key])==count,(key,len(groups[key]),count)
    result.append(dict(group=key,title=title,count=count,assessment=note,rows=groups[key]))
(OUT/'expanded-baseline-classification.json').write_text(json.dumps(dict(
    scope='All51 newly exposed BASELINE directed rows, grouped through bounded source inspection. These are not51 new head rows; final25 evidence follows separately. No exhaustive legacy-debt review or acknowledgement.',
    groups=result),indent=2,ensure_ascii=False)+'\n')
labels=sorted({r[k] for rows in groups.values() for r in rows for k in ['a','b']})
(OUT/'expanded-baseline-endpoints.json').write_text(json.dumps([index[k] for k in labels],indent=2,ensure_ascii=False)+'\n')
tails={}
for label in ['CounterProg.lean::tapes_update','CounterProg.lean::heads_update','CounterProg.lean::apply_act','CounterProg.lean::back_walk']:
    raw=index[label]['normalized_body']; assert 'omit[' in raw
    tails[label]=dict(raw_chars=len(raw),portion_before_omit_chars=len(raw.split('omit[',1)[0]),raw_body=raw)
(OUT/'parser-scope-tail-limit.json').write_text(json.dumps(dict(
    directive_tails=tails,
    other_tail='PolyTimePrefix.dropPrefixByLength raw body ends with endComplexity; Deterministic.visitedByTapeHead_step_subset includes endSpace/openCfg.',
    disposition='Unmodified tool outputs and denominators stay intact; semantic review distinguishes trailing scope commands from proof text. No alternate/repaired tiling run.'),indent=2,ensure_ascii=False)+'\n')
print('Classified all51 expanded baseline rows into17 bounded groups; full endpoint bodies retained.')
