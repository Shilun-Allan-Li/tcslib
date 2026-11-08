from pathlib import Path
import json,re,hashlib,datetime
P=Path('/private/tmp/sg1-round3-return-review');H='79e7c63a6bfa5f002663924f5c7d4e72db705026';K='f07808363a5fc839de9cdb1c90e05158826bbf57'
def sha(b):return hashlib.sha256(b).hexdigest()
d=json.loads((P/'live-prefix-candidates.json').read_text());special={
'sat_live_prefix':('confirmed exact F4 implementation','Direct Bool specialization of public backward liveness; replace body with the public theorem, keep header.'),
'clA5_live_prefix':('confirmed exact F4 implementation','Same exact specialization/proof; same mechanical replacement.'),
'expandTM_run_ofCfg':('already canonical public reuse','CounterLoop1777 directly applies runFrom_state_ne_none_of_le; no local implementation.'),
'satStop_clean':('forwarding consumer','Obtains hl by calling sat_live_prefix; the surrounding lockstep induction does not reconstruct the generic fact.'),
'clA5Stop_clean':('forwarding consumer','Obtains hl by calling clA5_live_prefix; preserve its caller contract and forward through the repaired helper.'),
'dg_all_inputs':('distinct halted-tail head bound','At2156 uses absorption after an already halted simulator endpoint to extend head bounds to later times; it does not infer earlier liveness from a live endpoint.'),
'sweep_run_to_halt':('liveness supplied as premise','Simulation theorem assumes all t<tau are live; it does not establish backward liveness.'),
'dg_simulate':('liveness supplied as premise','Window/Segment simulator assumes a live native prefix and builds a resource span.'),
'satHost_call':('liveness supplied as premise','Positive clean-call prefix is an explicit input to the host lifting, not derived from a later live state.'),
'clA5Host_call':('liveness supplied as premise','Same host-lifting contract; source hg already provides the first-halt cut.'),
'SatClean':('contract definition','Defines the positive clean-call premise; no proof implementation.'),
'CLA5Clean':('contract definition','Defines the positive clean-call premise; no proof implementation.'),
'satStop_step':('one-step local assumption','Case split consumes hlive:c.state!=none at this one configuration; no temporal prefix inference.'),
'clA5Stop_step':('one-step local assumption','Case split consumes supplied current-state liveness, not backward liveness.'),
'satAppend_clean':('separate first-None adapter consumer','Constructs its endpoint by phase composition and consumes sat_call_first_halt; no independent general backward-liveness recipe.'),
'clA5Copy_clean':('separate clean-stop consumer','Uses clInput_first and the positive release adapter for a concrete clean copy; no general backward-liveness reconstruction.')}
for n in ['sat_first_halt','sat_call_first_halt','clA5_call_first_halt','one_work_tape']:
 special[n]=('distinct first-None-halt selection','Selects a least halted time (and endpoint/output/positivity as stated), rather than inferring every u<=t is live from a live endpoint. This review does not extend FE-LIVE-1 or dispose of this separate family.')
for n in ['clBank_first','clCopy_first','clRow_first','clCmp_first','clFirst','clA5Compare_compute']:
 special[n]=('distinct fixed-LIVE endpoint selection','Fixed live stop/comparator endpoint and earlier-stop exclusion have their own premises and FE-LIVE-1 by-kind boundary. No generic backward-liveness reconstruction is established here; keep the existing named-union accounting, including inline context, unchanged.')
rows=[]
for r in d['candidates']:
 category,why=special.get(r['declaration'],('different concrete run/phase contract','Inspected run-addition/liveness contexts compose concrete machine phases or establish a concrete halt/output endpoint. No generic later-live-to-earlier-live implication is reconstructed.'))
 ls=r['chunk'].splitlines();ix=set()
 for ns in r['hits'].values():
  for n in ns:ix.update(range(max(0,n-r['start_line']-2),min(len(ls),n-r['start_line']+3)))
 rows.append({k:r[k]for k in ['path','declaration','start_line','end_line','sha256','hits']}|{'disposition':category,'reason':why,'source_quotes':[{'line':r['start_line']+i,'text':ls[i]}for i in sorted(ix)]})
assert len(rows)==84 and sum(r['disposition']=='confirmed exact F4 implementation'for r in rows)==2
(P/'live-prefix-candidate-dispositions.json').write_text(json.dumps({'source':H,'all5_files_scanned':True,'candidate_count':84,'exact_F4_implementations':2,'bounded_not_global_exhaustion':True,'all_candidate_dispositions':rows},indent=2,ensure_ascii=False)+'\n')
finite=(P/'source79/TCSlib/Complexity/TuringMachine/Finite.lean.txt').read_text()
def proof(text,name):
 m=re.search(r'(?m)^(?:private )?(?:lemma|theorem) '+re.escape(name)+r'\b[\s\S]*?(?=\n\n/--|\Z)',text);assert m
 chunk=m.group();header,body=chunk.split(':= by\n',1);return header,body,chunk
publichead,publicbody,publicchunk=proof(finite,'runFrom_state_ne_none_of_le')
checks=[]
for path,name,line in [('TCSlib/Complexity/ClassNP/SAT.lean','sat_live_prefix',3904),('TCSlib/Complexity/CookLevin/Hardness.lean','clA5_live_prefix',6229)]:
 text=(P/'source79'/(path+'.txt')).read_text();header,body,chunk=proof(text,name);normal=lambda s:re.sub(r'\s+','',s)
 assert normal(body)==normal(re.sub(r'\bcfg\b','c',publicbody))
 checks.append({'path':path,'name':name,'line':line,'header_sha256':sha(header.encode()),'proof_body_sha256':sha(body.encode()),'literal_header':header,'literal_body':body,'normalized_public_proof_cfg_to_c_equal':True,'complete_replacement':'exact Turing.MultiTapeTM.runFrom_state_ne_none_of_le tm c t ht','source_type_mapping':'k→k, Symbol→Bool, State→S, input→x, cfg→c, t→t, ht→ht; conclusion unchanged for every u<=t','no_new_API_import_statement_machine_or_runtime_change':True,'not_independently_elaborated':True})
(P/'F4-exact-contract-check.json').write_text(json.dumps({'source':H,'canonical_path':'TCSlib/Complexity/TuringMachine/Finite.lean','canonical_line':201,'canonical_header':publichead,'canonical_proof':publicbody,'canonical_not_counted_as_copy':True,'members':checks,'ledger_watch_source':K,'no_covering_ruling':True,'no_debt_permission_question_needed_for_mechanical_reuse':True},indent=2,ensure_ascii=False)+'\n')
# The current report has three prior-finding note rows plus N1..N23.
notes=[
('F1','Accept resolved in its stated scope','The two current cut helpers explicitly construct Segment with singleton forbidden anchor and True heads, compose the exact supplied seam and project segment_iff. Retained forwarding declarations are not retained concatenation implementations.','repaired-proof-and-contract-quotes.md'),
('F2','Accept repaired; retirement on merge','All five SAT, eleven Hardness and one Tautology bodies are present at source79. Basic closures are direct public applications; map/drop equations are serialized public readers, field bounds split malformed input, and Tautology directly consumes exact on-image composition. F4 is a separate kind.','repaired-proof-and-contract-quotes.md;receipts-screen-family-check.json'),
('F3','Accept corrected accounting','Six SingleTape declarations contain twelve Segment replacements in the stated3/1/2/2/3/1 distribution; with Tautology10 and CounterLoop3, original total25. Original issued records remain historical.','issued pack and immutable packet bindings'),
('N1','Accept','All1614 rendered sections,521 JSON sections, exact ordering/uniqueness, four exchange checksums and mixed source79/recordsf078 bindings were independently checked against immutable Git blobs.','packet-verification.json;all1614-section-bindings.json'),
('N2','Accept exact definition','Segment has exact run endpoint, strict forbidden-state cut and closed full-vector head predicate. Its endpoint need not be live/halted; time0 has no strict-cut requirement.','repaired-proof-and-contract-quotes.md'),
('N3','Accept bounded specializations','Tautology uses forbidden live anchor/True heads; CounterLoop keeps joint counter/body head witnesses and done/escape exclusions; SingleTape has closed sole-head interval and no forbidden states. Bridges/public contracts are preserved.','source79 captures;compiled-evidence-check.json'),
('N4','Accept boundary analysis with execution limit','Zero/initial/final anchor, earlier halt, closed endpoint heads, inverted interval and correlated-vector counterexamples follow from the literal clauses. The auditor reports78125 finite model cases; this review does not rerun or promote that finite sanity check to Lean evidence.','Segment definition and issued audit N4'),
('N5','Accept literal contracts','PolyTimeComputable has one finite binary machine and polynomial budget; native input/blank work/output conventions are unchanged. Pair encoding/decoder defaults and length-based drop match the source interfaces.','repaired-proof-and-contract-quotes.md;all50-current-source-captures.json'),
('N6','Accept all5 SAT mappings','Pairing keeps original input for both fields; mapSnd includes malformed→[] through the total equation; append/unary use exact public closures.','repaired-proof-and-contract-quotes.md'),
('N7','Accept all8 Hardness basic mappings','Linear/map/pair/append/poly-unary/constant/conditional/conjunction premises and singleton Boolean outputs match current private headers; no closure witness reconstruction remains in these bodies.','repaired-proof-and-contract-quotes.md'),
('N8','Accept final3 specialized mappings','Decoder failure gives empty fields; success uses public inverse plus joint length bound. Comparison pairs g before f; prefix drops length(u x) from s x. Same-home change is separate from foreign reads; both precise imports have recorded approvals.','repaired-proof-and-contract-quotes.md;immutable import-ruling records'),
('N9','Accept exact raw on-image replacement','Tautology applies exists_comp_on_image with arbitrary M/U, image-only correctness and original-input T2 budget, exactly2*T1+T2+2. It adds no totality/monotonicity premise. The four gone screen rows represent one implementation.','repaired-proof-and-contract-quotes.md;packet-bound on-image sweep'),
('N10','Accept adversaries with execution limit','Empty/malformed10 projections are empty; valid01 is the empty pair, lenLe defaults true, reversed unary construction has correct direction and overlong drop is empty. Auditor finite counts2047/961/81 are self-reported sanity execution; no numerical rerun here.','issued source definitions and audit N10'),
('N11','Accept exact bounded controls/seals','Independently reconciled old4 controls plus36/40/42/final42/28 positive kernel names and exact negative rfl goal/error identities. The measured actual-section scope and documented abbreviation/projection limits remain; imported theorem implementations/global legacy proofs are not certified opaque.','receipts-screen-family-check.json'),
('N12','Accept source/compiled distinction','All50 full25 captures match Git source3023/79. Source header/term/attribute freeze records remain exact packet data; compiled all1351 nonprivate records agree independently. Exactly five Lean files and only the explicitly approved imports/private bridges are claimed.1986 source declarations are not7101 compiler constants.','all50-current-source-captures.json;compiled-evidence-check.json;packet-bound complete header freeze'),
('N13','Accept complete compiled accounting','Reparsed all six raw native streams, full raw types, CI/reflected attributes, allAX/publicAX and effective simp rules:7101→7063,5750→5712private,1351nonprivate exact,168simp rules exact,+6/−44 private only,10shared private generated type changes. Proof values/arbitrary extension state are not compared.','compiled-evidence-check.json'),
('N14','Accept scoped axiom result','ALLAX exactly covers census and PUBLICAX its nonprivate subset. All43 roots+93descendants=136 distinct are standard-or-subset. All9 inherited Primitives nonstandard closures remain exact; sole shared axiom change drops choice from clA5Pair_sizes.','compiled-evidence-check.json'),
('N15','Accept existing6-kind boundaries','Clean/lifting, positive-release, padding, finite one-way transducer, specified bridge polynomial and shared-bank dispatcher kinds retain their exact prior approvals, maintainer ownership and next12.2c window. They do not cover the general backward-liveness watch.','ledger-at-issued-records.md;immutable six-kind records'),
('N16','Accept separate7th ruling','The explicit accepted unary-clock-host ruling covers its14 named existing host/actual-orbit members, disjoint from prior35. Public all-word/fixed-monomial assumptions do not automatically follow from private actual-orbit/data-dependent clock premises. No new API/future host is authorized.','receipts-screen-family-check.json;packet-bound ruling.json'),
('N17','Accept historical source-specific status and exactFE limits','At audited source79 #234 APIs are absent/unused. FE-LIVE-1 covers whole-config fixed live stops, including both comparator verdicts, separately from None halts and backward liveness. Current user merge of#234 changes future context only; do not rewrite this old result. Five Hardness names are disjoint from prior49.','receipts-screen-family-check.json;ledger-at-issued-records.md;all50-current-source-captures.json'),
('N18','Accept bounded residual assessment; F4 remains real','clNative_image assumes second-stage correctness only on f-image and already calls bufferedCompTM_computesInTime; total FP.comp does not directly match. Other watches retain distinct statuses. Stable rows grant no acknowledgment; F4 is now an exact canonical match.','repaired-proof-and-contract-quotes.md;F4-exact-contract-check.json'),
('N19','Accept named-union arithmetic and limits','10/26=38.46% canonical overlap; SAT34/270 and Hardness35+14+5=54/544 are named mixed-disposition lower bounds. Set disjointness checked; clA5_live_prefix already belongs to prior union, so F4 adds no new member. Do not subtract16 closure repairs or count54 as confirmed copies.','receipts-screen-family-check.json;packet-bound family-accounting.json'),
('N20','Accept full screen data without tiling rerun','Exact1956→1947 spans/2013→1995 candidates; all35delta identities classify2new/20gone/13changed.435 term normalized spans and259 term candidate rows agree (byte offsets may shift after earlier proof edits). Raw metrics/parser-tail limits retained; stable candidates are not exemptions.','receipts-screen-family-check.json;packet-bound raw candidate and index data'),
('N21','Accept actual chained replay lineage; not current refresh','Receipts/raw rows/orders/hashes match329atD0+26at63+2at79 with357 actual-j4 launches and static66/0/0. Whole-clone provenance is preserved; it is not a single final329 execution or an admission-free campaign. F4 repair/current campaign needs new replay or an explicit valid current-source argument; root plans fresh replay.','receipts-screen-family-check.json;immutable drivers/receipts'),
('N22','Accept fidelity and explicit execution limits','40substitutions→31encodings and3binary companions roundtrip exactly.19 files-schema manifests/786payload entries verify; additionally the distinct artifacts-schema gate119 return manifest has22entries (20 manifests/808entries checked here). Three screen checksum generations, graph helper, lint/old-failure chronology remain immutable data. No supplied script, Lean, tiling, CLI lint or blueprint run here.','packet-verification.json;bundled-manifest-checks.json'),
('N23','Accept notation only','Local symbol meanings/source pins in the glossary match their declarations. No new mathematical or procedural claim follows.','issued findings and exact source pins')]
assert len(notes)==26 and{n[0]for n in notes}=={'F1','F2','F3'}|{f'N{i}'for i in range(1,24)}
records=[{'id':'F4','severity':'major','disposition':'Confirmed; repair required, not closed by this review','assessment':'Both exact public specializations can be forwarded without a new premise/import/API/statement. Watch and accepted-family boundaries do not authorize retention. Parent owns source repair, scoped opacity, current replay and external round4.','evidence':'F4-exact-contract-check.json;live-prefix-candidate-dispositions.json'}]+[{'id':i,'severity':'note','disposition':disp,'assessment':why,'evidence':ev}for i,disp,why,ev in notes]
(P/'per-finding-dispositions.json').write_text(json.dumps({'findings_sha256':'a98e9f12d2e5b75c270edf0e28cc79783505c7b6163cbeacb50536204b1d2cc6','source':H,'records':K,'verdict_supported':'HOLD0/1/0/26','all27_rows':records,'no_debt_accepted_by_reviewer':True,'no_closure_or_merge_action':True},indent=2,ensure_ascii=False)+'\n')
table='| ID | Disposition | Assessment |\n| --- | --- | --- |\n'+''.join('| '+i+' | '+disp+' | '+why.replace('|','\\|')+' |\n'for i,disp,why,_ in notes)
review='''# Gate106 round3 returned audit — independent review

**Not yet clear to merge: #215.** The returned HOLD0 blockers/1 major/0 minors/26 notes is
supported. F4 is a concrete exact public-reuse defect; the current source/evidence does not
need another debt acknowledgment. The previous F1/F2/F3 repairs remain valid in their stated
scopes. All26 note dispositions appear below and in per-finding-dispositions.json.

The received report is preserved verbatim:23261bytes, SHA256
`a98e9f12d2e5b75c270edf0e28cc79783505c7b6163cbeacb50536204b1d2cc6`.
This review treats it, supplied programs and prior reports as data. It writes only its new
review folder/private scratch and performs no Lean, source/Git/canonical mutation, screen,
merge, gate closure or debt-acceptance action.

## Actual F4 contract and required disposition

At audited source `79e7c63a6bfa5f002663924f5c7d4e72db705026`, SAT3904 `sat_live_prefix` and
Hardness6229 `clA5_live_prefix` state exactly the Bool specialization of the already available
public Finite201 `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`:

```lean
(tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
(ht : (tm.runFrom c t).state ≠ none) :
∀ u ≤ t, (tm.runFrom c u).state ≠ none
```

Both five-line proof bodies are exactly the public proof after cfg→c and whitespace removal.
They split t at an earlier u, use halted-tail absorption, then contradict endpoint liveness.
The full replacement is:

```lean
exact Turing.MultiTapeTM.runFrom_state_ne_none_of_le tm c t ht
```

Every argument and conclusion matches: k, Bool, S, native input x, complete configuration c,
t and ht; no extra endpoint/fixedness/positivity premise is needed. The existing import
context already contains the theorem. Keep both private headers/visibility and caller
contracts; updating the short doc to name the canonical theorem is appropriate. This is a
source/type mapping, not an elaboration performed by this reviewer. Root owns the actual
mechanical edit and native/scoped/current replay evidence.

The issued ledger at records `f07808363a5fc839de9cdb1c90e05158826bbf57` expressly calls generic
live-prefix copies a Watch. None of the six adapter/dispatcher acknowledgments or the
separate seventh unary-clock-host ruling covers this general temporal fact. FE-LIVE-1
selects a first fixed LIVE-stop entry while preserving its complete endpoint. Backward
liveness from a live endpoint needs neither that specified stop nor its fixedness premise;
it is a separate public contract. A named affected union is not permission to retain every
fact in that union. F4's names already belong to the receiving-file lower bounds, so their
confirmation does not add another member or crossing.

The standing mechanical-reuse procedure supplies authorization to repair the exact bodies
in the same PR without asking for a new API/debt/design decision. Do not silently upgrade the
watch to accepted debt. F4 remains open until root records the actual source fix and required
current evidence; this review itself does not mark it resolved.

## Bounded all-five-file same-kind inspection

The inspection uses the exact audited source79 bytes for SAT, Hardness, Tautology, CounterLoop
and SingleTape. It retains all84 conservative declaration candidates, full source chunks,
line locations, hashes and per-candidate dispositions. Enumeration includes every occurrence
of runFrom_of_halt, runFrom_add, Nat.add_sub/exists_eq_add, live/Halted/state-none forms and
contrapositive/least-time contexts; candidates are not filtered to a single tactic spelling.
Source-span tails may include a following docstring; exact F4 body hashes stop before it.

Only the two reported helpers implement this precise general backward-liveness contract.
CounterLoop1777 already directly calls the public theorem. SAT/Hardness Stop_clean merely
consume the two private helpers, so forwarding those helpers repairs their reuse path.
The other absorption hits are least-None-halt selection, fixed-LIVE-stop selection or
SingleTape2156's extension of a head bound after an already halted endpoint. Other run-add
hits concatenate concrete phases. Full statements, relevant inline closures and their
premises were inspected; no additional exact F4 repair was identified in this bounded
population. This is candidate enumeration plus inspection, not global semantic exhaustion
or a new disposition for the separate first-None family.

## Packet and supporting evidence

The report correctly audits pre-#234 source79 and comparison base
`3023dc1408c3d216fc07a7cbba9ae30135b861ed`, with issued records
`f07808363a5fc839de9cdb1c90e05158826bbf57` and exchange
`f37dab00e3e04b396eb9cf130d3a738385653f71`. All full commit objects were resolved and checked.
The later user merge of#234 changes the upcoming proof/replay context; it does not alter the
meaning of this immutable audit. In particular the report's absent/unused/unmerged#234
remarks are true at the audited source and publication generation.

Independent reconstruction checked all1614 rendered sections, exact order/uniqueness,
all521JSON sections and raw mixed-pin Git blob bindings. Every TCSlib path comes from
source79; every other path comes from issued records. The100861434-byte bundle SHA256 is
`104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8`.
All four exchange checksums,50plaintext current source captures,40→31lossless substitutions,
three binary companions,17declared complete folders and preserved1539/1609prefix selections
match. The graph helper is byte-exact and present. All19 files-schema manifests/786members
verify; the additional artifacts-schema gate119 review manifest contributes22members, for
20manifests/808checks here. These are differing schema-count conventions, not a missing input.

The complete six compiler streams were decoded and independently reparsed, including all
226721273bytes of raw type payload, structural CI, reflected attributes, ALLAX/PUBLICAX and
168effective owned simp rules. Counts7101→7063 and nonprivate1351→1351 agree. All nonprivate
fields agree; +6/−44changes are private,10shared raw-type changes are private generated
auxiliaries and the sole shared axiom change drops choice from clA5Pair_sizes. All43current
roots plus93descendants=136distinct constants are standard-or-subset; nine inherited
Primitives nonstandard closures remain exact. No proof-value or arbitrary extension-state
equality is inferred.

Control identity checks reconcile the old two-definition/four-control generation and every
36/40/42/final42/28 positive kernel name and exact intended negative error/goal identity.
The supplied native receipts remain supplied executions. The actual bounded seals do not
cover all unchanged legacy proofs or recursively certify imported theorem implementations.
The complete raw source-screen data agrees with1956→1947eligible spans,2013→1995directed
candidates and2new/20gone/13changed identities; all435term normalized spans and259term
candidate rows agree. Literal offsets can change after earlier proof edits; normalized term
bodies and raw metrics are retained. No tiling or numerical adversary model was rerun.

The replay chain's329/26/2successful rows, all357effective-j4 launches, exact orders, receipt
hashes and static66/0/0totals reconcile. Whole-clone provenance and distinct D0/63/79 heads
remain as recorded. It is not one final329-module run or an admission-free campaign.
These immutable source79 statistics and MSG7 results must not be relabeled as the repaired,
post-#234 current source. Root owns that integration/current replay, any refreshed metadata,
scoped F4 controls and forthcoming Codex round4 packet/dispatch. Selection of Codex for R4
was relayed by root; no external dispatch is performed here.

## All26 note dispositions

'''+table+'''

No further concrete source, packet-binding, compiler/control/replay accounting correction was
identified in this bounded returned-audit review. Preserve the returned HOLD verbatim and
record F4's mechanical repair/current evidence separately; acceptance of the26scoped notes
does not close the major or grant merge approval.
'''
(P/'REVIEW.md').write_text(review)
(P/'scope-and-execution.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':H,'records':K,'output_only':'campaign/gates/106-sg1-dedup/review/round3-return-review/ and private scratch','report_verdict_supported':'HOLD0/1/0/26','same_kind_files':5,'conservative_candidates':84,'exact_F4members':2,'new_debt_request_needed':False,'not_run':['Lean','delivered scripts','screens/full tiling','numerical adversary reruns','CLI lints','current merged replay','source/Git/canonical mutations','gate/merge/debt action'],'MIG_BASE_checkpoint':'Separate authorized prior job completed103.483s againstMAC5 before this review; its own scratch/receipts preserved. No MIG HEAD run.','R4_agent_choice':'Root relayed user selected Codex; parent owns staging/dispatch.'},indent=2)+'\n')
print('review_bytes',len(review.encode()),'note_dispositions',len(notes),'candidate_dispositions',len(rows))
