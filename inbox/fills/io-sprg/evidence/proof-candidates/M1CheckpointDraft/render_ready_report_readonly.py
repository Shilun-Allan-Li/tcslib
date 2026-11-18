"""Assemble the completed M1 checkpoint prose and preserved archive tables. No Lean/git."""
from pathlib import Path
import json,hashlib,csv
b=Path('/private/tmp/io-sprg-proof-notes/M1CheckpointDraft')
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
s=json.loads((b/'snapshot.json').read_text())
o=json.loads((b/'overlap-log-review.json').read_text())
static=json.loads((repo/'evidence/checks/m1-final/summary.json').read_text())
freeze=json.loads((repo/'evidence/checks/m1-final/freeze-summary.json').read_text())
head=static['head'];assert head=='19dde91afc384656e7e47cb018057e088d4ded0a'
assert s['M0_original_filled']==100 and s['M0_original_remaining']==46
assert len(s['new_named_theorems'])==3 and all(not x['direct_sorry']for x in s['new_named_theorems'])
assert s['recorded_step_count']==103 and not s['changed_while_reading']
assert all(x['source_hash_matches']and x['all_standard_axioms']for x in s['owner_summaries'])
assert sum(x.get('public_theorems')or x.get('new_helpers')or 0 for x in s['owner_summaries'])==297
build=[]
for line in(repo/'evidence/build/M1/all-owners/results.jsonl').read_text().splitlines():
 r=json.loads(line)
 if'module'in r:build.append(r)
assert len(build)==23
assert all(r['rc']==r['errors']==r['error_forms']==0 and r['head_at_start']==head for r in build)
assert all(hashlib.sha256((repo/(r['module']+'.lean')).read_bytes()).hexdigest()==r['source_sha256']for r in build)
headline=json.loads((repo/'evidence/checkpoints/M1/headline-axioms.json').read_text())
assert headline['head']==head
standard=[n for n,a in headline['axioms'].items()if'sorryAx'not in a]
assert len(headline['axioms'])==19 and len(standard)==4
slots=json.loads((repo/'evidence/host/M1-final/slot-summary.json').read_text())
assert slots['acquisitions']==1068 and slots['max_concurrent_job_wrappers']==2
assert slots['post_correction_serial']and not slots['active']
text=f'''# io-sprg Phase A — M1 algebraic correctness checkpoint

M1 proof work and local checks are complete at `{head}`. All 100 original bodies in
this checkpoint and three new theorem-only helpers are filled, with 103 checked step
records. All 23 owned modules pass a fresh full build at this source head. Across
11 affected owners, 297 public theorem axiom prints contain only standard axioms.
Forty-six original theorem bodies remain for M2–M6. T1–T6 remain named, unproved
Phase B obligations. This is an M1 checkpoint, not final Phase A completion.

M0 remains frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7`; its report and delivery
are preserved under `evidence/checkpoints/M0/`. Current static checks pass as detailed
below. M1 packaging/push receipts are bound by the root delivery metadata. The final
full kernel census, transitive sorry graph and complete Rule10 matrix have not been
rerun for M1 and remain final-completion gates; the M0 results are historical only.

## Bases, scope and milestones

- Lean base: `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`.
- Records: `dbea2807532392781304e004715f3b0190025f5e`.
- Host inputs: `bc9d982b83cb35ea351e2fb373752e8688945b1c`.
- Rule10 provenance: `2467bc3befdad8472b1f359337bf3a203e3651e1`.
- M1 source head: `{head}`.
- Source: 23 owned Lean files, 7,244 lines; existing root export import retained.
- Fresh decls2: 673 ADDED. Frozen M0 declarations: zero CHANGED/REMOVED, three helpers added.

| Milestone | Status |
| --- | --- |
| M0 statements | Complete and frozen; archived checks and payload preserved. |
| M1 algebraic correctness | Complete proof/local-check checkpoint: original100 + helpers3. |
| M2 stretch | Next: all four remaining Stretch obligations, including SP-W3 seed growth. |
| M3 Claim4.2 | Pending; common cutoff must remain before every public prime. |
| M4 reductions / prop41 | Pending; every-realizer inequalities and exact nuisance law. |
| M5 raw Theorem4.1 | Pending; conditional security/existence. |
| M6 links / assembly | Pending; early Encoding17 support is proved, target truth is not asserted. |

## Completed proof work and current checks

| Owner / group | Original bodies filled | New helpers | Public theorem prints, standard-only |
| --- | ---: | ---: | ---: |
| Raw LPN | 3 | 0 | 34 |
| Degree | 24 | 0 | 26 |
| Params | 14 | 0 | 45 |
| Basic | 0 | 2 | 2 |
| Encoding | 17 | 0 | 48 |
| Buckets | 7 | 0 | 13 |
| SparseFactor | 5 | 0 | 11 |
| Polys | 10 | 0 | 27 |
| Correctness | 18 | 1 | 19 |
| Defs | 1 | 0 | 29 |
| Samplers | 1 | 0 | 43 |
| Total | 100 | 3 | 297 |

The Defs efficiency-forgetting bridge and Samplers prime-width bound are included.
The two new Basic results specialize the actual fixed-width tagged-list code; the
new G4_seed_allOutputs theorem preserves the specific G4 witness for later T2 links.
They introduce no algorithm, sampler, machine, encoder or efficiency assumption.
Basic imports the already-used Uniform owner and adds no Mathlib root. The private
prefix-free/variable-size overlap and public append/list/vector reuse remain disclosed.

| Check | Current evidence |
| --- | --- |
| Full owner build | 23 records, rc0/errors0 in both forms; all source hashes and head match. `evidence/build/M1/all-owners/results.jsonl`. |
| Filled/remaining bodies | 103 CHECKED_PASS steps; original100 filled, original46 direct holes remain. `evidence/steps/`, `source-obligations.tsv`. |
| Owner axioms | All297 standard-only, no sorryAx; current source-hash-matched `evidence/checks/M1-*/summary.json`. |
| Headline axioms | Fresh19 prints; G4_eval_eq, jls_hasComplexity, lpnNoise_law and PrimeSchedule.nonempty are standard-only. The other15 later-phase/assembly headlines retain sorryAx. `evidence/checkpoints/M1/headline-axioms.json`. |
| Frozen declarations | M0 changed0/removed0; exactly the three new helpers. `evidence/checks/m1-final/freeze-summary.json`. |
| Static gates | decls2/style/sk15/clash rc0; 673 ADDED, zero clashes; zero new individual campaign FAIL/WARN lines against base. Campaign aggregate rc1 reflects baseline findings. `evidence/checks/m1-final/summary.json`. |
| Widths/sizes | All widths pass; 23files/7244lines; maximum file{ s['max_lines'] }lines and maximum width{ s['max_width'] }. |
| Tagged slots | V2 audit covers1068 acquisitions; max2 retains the exact known incident. Post-correction tagged acquisitions are serial and no reservation remains active. `evidence/host/M1-final/slot-summary.json`. |

All full-build and owner-summary bindings above were read from saved root-run evidence;
this report preparation ran no Lean. Owner theorem prints are not represented as a
complete new kernel census. M0's1036 stored constants/948 public types/511 theorem
prints and265 transitive sorry dependents are not current M1 counts. The remaining
full-graph, implicit-axiom and final public-type census must be regenerated at completion.

M0's88 seal probes and96 paired controls (184 runtime probes) passed at M0. Those
runs bind the M0 source/olean environment and are retained as historical results.
The complete four-variant matrix, requests/masks/EOF attribution, controls and final
import-environment binding have not been rerun at M1. Include Basic and every later
new owned helper file in the final collectors and seals. No current M1 full-seal
success is claimed. Final replay/bundle/manifest and exchange receipts belong to the
root checkpoint packaging; they are not inferred from the M0 delivery.

## Remaining inventory and next milestone

The 46 original direct holes consist of M2:4, M3:10, M4:8, M4/M6 advice support:8,
M5:7 and M6 links:9. Seventeen Encoding support obligations are completed early.
The complete current per-body list is `source-obligations.tsv`; this source inventory
does not estimate the remaining transitive sorry graph.

The next M2 scope is ALL four remaining declarations in Stretch.lean:

- Params.seedBitsAt_le.
- jls_seedBits_eq.
- jls_seedBits_le.
- jls_hasPolyStretch, retaining eventual kappa<=seedBits and the common power bound.

No existing mathematical definition, theorem statement or target quantifier order
changed after M0. Current frozen-declaration checks preserve every existing name and
header. The rational-delta SP-W1 ruling, acceptance-level SP-W2 correspondence and
growing-seed SP-W3 predicate remain as frozen. Optional empty grids, deterministic
sparse factors, faithful canonical encodings and the uniform-prime scopes are retained.
The proposed future LPN module split is a plan, not a delivered M1 source change.

## Overlap searches and corrections

The saved-log snapshot at {o['captured_utc']} contains218 searches, each with matching
saved source/log hashes: 20 closed;68 valid partial suggestions;92 completed exact
searches without a closing proof;9 clean apply no-hits;17 bounded timeouts;8 statement
elaboration errors;4 scope errors. These are per-log categories in
`overlap-log-review.tsv/json`, not a claim of mathematical theorem absence.

record_overlap.py's DIAGNOSTIC_FAILURE label covers several outcomes. Clean apply
no-hits differ from heartbeat timeouts and malformed goal statements. Failed candidate
attempts can appear before a valid final partial suggestion; rc0/errors0/sorry1 remains
partial, never a closing proof. Bounded searches use100000 heartbeats and cannot
establish absence or success. Owner proofs retain their separate unrestricted budget.
The original seven timeout rows are a historical subset; later Algebra/LPN logs are
classified individually. Source/header errors never count as completed overlap searches.

All old faulty records remain saved, with exact superseding source/log hashes in
`supersession.tsv/json`:

- Algebra_firstGood_none_iff/some_flag -> their AlgebraV2 names, both modes. Remove
  the unnecessary BigOperators scope opening rather than adding an unused import.
- BucketsSparse_sparseFactor_mul and sparseFactor_mul_of_card_le -> the respective
  BucketsSparseV2 names; Algebra_oneSd_factors_mul -> AlgebraMatrixV2_oneSd_factors_mul.
  Explicit Matrix annotations repair the HMul goal errors. New exact runs do not
  close; new apply runs give partial suggestions. Actual SparseFactor source proofs
  separately have standard11 owner prints.
- Algebra_G4_eval_eq -> AlgebraSupportV2_G4_eval_eq, both modes. The old Type* binders
  violated the Type0 OracleSpec/OracleComp API. The corrected finite-construction
  Type0 goals elaborate but BOTH searches time out; this is not a no-hit result.

Other corrected SupportV2 goals were used directly; no older executed errors are
claimed for them. eval'_correct and Params.G4_seed_allOutputs have clean exact
nonclosure/partial apply outcomes; the expanded jls_hasComplexity goal closes by
existing witness logic. The bridge goals import no owned modules and abstract only
relevant reader predicates or the actual prime upper-width field. All library
self-hit exclusions and public API reuse remain recorded alongside the probes.

## Host/process history and qualifications

The whole-job two-subagent limit was breached when a child started a third research
descendant. Root interrupted it and prohibited further spawning/resumption. Reported
activity was source reading, rg and temporary notes, with no reported Lean/Lake/cache/
push/implementation mutation. This is task-context reporting, not an independent
process audit; duration was not established and is not characterized as brief.
See `evidence/host/team-limit-correction.json` and the archived M0 disclosure.

During M1 root also overlapped Params_B_pos apply with step029's owner check after
printing only exec_command.output and losing an ongoing session_id. The recorded
search runner93880/wrapper93883/child93887 overlaps owner wrapper93983 during the
confirmed15:07:45–15:07:48UTC interval. Root sent SIGTERM only to the recorded own
child; the search wrapper release is recorded at15:08:34UTC. The correction is to
preserve full session metadata, poll running sessions, bound diagnostic searches,
and start no new Lean until the existing runner exits. Exact facts are in
`evidence/host/search-process-correction.json`; no wider child-process history is inferred.

The fresh tagged-slot audit preserves that violation:1068 acquisitions, maximum2,
with299 post-correction acquisitions serial, maximum1 and no active reservation at
its snapshot. It audits tagged wrapper reservations, not all host jobs, actual
simultaneous child counts or a complete process history. It does not erase the earlier
violation or justify an unqualified whole-job seriality claim. Its source/log hashes
and REAP qualifications are in `evidence/host/M1-final/`.

The verified source remains jls26.pdf with SHA-256
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`, read in place only.
The PDF is not copied or delivered. M0's delayed memory-preflight and pinned tool/cache
provenance remain historical facts. The job retains the pinned slot wrapper/tag.
This preparation used source/evidence reads and temporary writes only, with no
Lean/git/cache command, source edit, spawn, or active/archived REPORT overwrite.

## Preserved fidelity, Rule15 and non-vacuity tables

The four tables below are reproduced VERBATIM from `evidence/checkpoints/M0/REPORT.md`.
Their source locations are explicitly FROZEN M0 anchors, not current M1 line numbers.
Their mathematical contracts and deviations remain unchanged. The current declaration
identity appendix resolves present M1 source locations, including shorthand fields.
`archived-table-bindings.json` records each original range and exact table hash.

Rule15 remains mandatory: Raw bundles claim no efficiency; BoolPRG supplies its
mandatory witnesses; efficient LPNFamily/SPRG values are constructed only through
conditional targets. T3/T5 concern the SAME complete draw. T6 selects one U/coin
polynomial/core before every dimension and prime schedule. No target is asserted true,
no product fair-coin sampler is built, and no Phase B efficiency proof is attempted.

'''
text+=(b/'archived-tables.md').read_text()+'\n\n'
text+='''## M1 theorem-only additions to the fidelity inventory

Basic's two fixed-width tagged-list results are shared mathematical encoding glue,
not additional paper theorems. G4_seed_allOutputs joins the exact algebraic/Boolean
support facts and retains the specific G4 witness. Their current anchors are in the
appendix. The pre-M0 SP-W1/SP-W2/SP-W3 rulings and all Dv1–Dv18 disclosures remain in
the archived report and route records; this checkpoint introduces no new assumption,
algorithm or changed binding statement.

The target definitions below are also reproduced from the archive; Targets.lean is
byte-identical to its frozen M0 source. They remain unproved Phase B propositions.
Their conditional M6 bridge theorems are among the remaining named obligations.

'''
text+=(b/'archived-target-definitions.md').read_text()+'\n\n'
text+=(b/'current-anchor-appendix.md').read_text()+'\n'
(b/'REPORT-M1.DRAFT.md').write_text(text)
(b/'REPORT-M1.READY.md').write_text(text)
(b/'ready-report-status.json').write_text(json.dumps({'source_head':head,'status':'M1_PROOFS_LOCAL_STATIC_CHECKS_COMPLETE_DELIVERY_METADATA_ROOT_PENDING','source_files':23,'source_lines':7244,'original_filled':100,'new_helpers':3,'checked_steps':103,'remaining_direct_original_holes':46,'affected_owner_theorem_prints':297,'fresh_owner_builds':23,'fresh_headline_prints':19,'fresh_standard_headlines':4,'full_kernel_census':'M0_HISTORICAL_FINAL_REFRESH_PENDING','full_seal_matrix':'M0_HISTORICAL_FINAL_REFRESH_PENDING','source_snapshot':s['captured_utc'],'saved_search_snapshot':o['captured_utc'],'archive_tables_preserved':4,'current_source_anchor_rows':len(json.loads((b/'current-declaration-anchors.json').read_text()))},indent=2)+'\n')
print('READY:',b/'REPORT-M1.READY.md','lines',len(text.splitlines()))
