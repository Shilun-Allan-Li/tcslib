"""Render a deliberately unsigned M1 draft from saved snapshots. No source/REPORT writes."""
from pathlib import Path
import csv,json
b=Path('/private/tmp/io-sprg-proof-notes/M1CheckpointDraft')
s=json.loads((b/'snapshot.json').read_text())
o=json.loads((b/'overlap-log-review.json').read_text())
new=s['new_named_theorems'];fillednew=sum(not r['direct_sorry']for r in new)
complete=s['M0_original_filled']+fillednew
body=f'''# io-sprg Phase A — M1 checkpoint DRAFT

Unsigned preparation snapshot at {s['captured_utc']}. M1 fill and its final gates are
still in progress. This draft does not replace evidence/REPORT.md or the archived
M0 report and does not claim that M1 has been frozen, packaged or pushed.

M0 remains frozen at `{s['M0_head']}` and its archived payload is in
`evidence/checkpoints/M0/`. The latest recorded progress commit is
`{s['latest_recorded_progress'].get('commit','UNBOUND')}`; this draft does not infer
that it equals the eventual M1 checkpoint head. ROOT MUST REBIND THE FINAL M1 HEAD.

## Checkpoint scope and proof counts

The complete planned M1 scope is 100 ORIGINAL theorem bodies plus three new
helper theorems: the two Basic fixed-width list lemmas and
Params.G4_seed_allOutputs. The original scope includes both
SPRG.Raw.HasComplexityEff.hasComplexity and Params.primeWidthBound; these are
mandatory, even though the early progress list omitted them. Seventeen Encoding
bounds/injections are classified in the frozen obligation table as M6/supporting
M1–M3; proving that support early does not complete M6 or prove any Phase B target.

| Owner / group | Planned original bodies | New helpers | Status at this snapshot |
| --- | ---: | ---: | --- |
| Raw LPN | 3 | 0 | Completed owner summary; standard axioms recorded. |
| Degree | 24 | 0 | Completed; all 26 public theorem prints standard. |
| Params | 14 | 0 | Completed; all 45 public theorem prints standard. |
| Basic | 0 | 2 | New owned module; both theorem-only helpers checked. |
| Encoding | 17 | 0 | Completed; 48 public theorem prints standard in V2 summary. |
| Buckets | 7 | 0 | Completed; 13 public theorem prints standard. |
| SparseFactor | 5 | 0 | Completed; 11 public theorem prints standard. |
| Polys | 10 | 0 | Completed; 27 public theorem prints standard. |
| Correctness | 18 | 1 | Root is filling; final owner/axiom summary pending. |
| Defs complexity bridge | 1 | 0 | Mandatory completion and fresh owner/axiom check pending. |
| Samplers prime-width bound | 1 | 0 | Mandatory completion and fresh owner/axiom check pending. |
| Total | 100 | 3 | Expected completed M1 work: 103 bodies, subject to final evidence. |

Static source snapshot: {s['M0_original_filled']} of the 146 original M0 holes have
bodies; {fillednew} new named helper bodies are present, totaling {complete} body
fills/additions. There are {s['direct_sorry_tokens']} direct source sorry tokens.
These are source observations, not a substitute for a fresh kernel/axiom census.
There are {s['recorded_step_count']} saved step records; their statuses are
{s['recorded_step_statuses']}. Earlier individual step checks bind earlier source
bytes and do not substitute for the final whole-owner/current-import-environment check.

If only this planned M1 scope is completed, 46 original direct holes remain for
M2–M6. Recompute that number if any additional body is filled. T1–T6 remain named,
unproved Phase B propositions throughout; proving conditional assembly links is
not proving their hypotheses. M2 stretch, M3 Claim4.2, M4 reductions, M5 security
and M6 links/assembly remain later milestones unless separately checked and claimed.

## Source and unchanged mathematical interface

The captured source set contains {s['source_files']} owned Lean files and
{s['source_lines']:,} lines, plus the existing root export edit. Largest file:
{s['max_lines']} lines; maximum width: {s['max_width']} characters. M0 had 22 owned
source files; Basic is the one new owner. The complete source hashes and per-file
M0 comparison are in snapshot.json. Refresh these measurements after root finishes.

Basic contains only two specialized fixed-width tagged-list theorems, shared by
Encoding and later advice proofs. It imports the existing Uniform owner, introduces
no new Mathlib root, and reuses public nil/cons, append and modular vector APIs.
Private generic prefix-free/variable-size overlap remains explicitly disclosed in
proof-candidates/FixedWidthList/README.md. No private symbol, encoder algorithm or
sampler is copied. The specific G4 support helper is theorem-only logical glue in
Correctness, preserving the literal G4 witness for later T2 complexity assembly.

No post-M0 existing definition/statement change is intended. Checked-owner summaries
record frozen-header preservation; final full typed comparison is still required.
The rational-delta ruling, acceptance-level SP-W2 repair, growing-seed SP-W3
predicate, optional empty-grid positions, deterministic row-major factors, canonical
assumption encodings and all efficiency quantifier orders remain as frozen at M0.
The proposed later LPN file split is only a plan and is not part of this captured M1
source set. Do not list its four child modules as delivered owners.

## Fidelity, Rule15, non-vacuity and Phase B tables

Carry forward the MATHEMATICAL CONTENT of the archived M0 fidelity table, Rule15
primitive/efficiency table, field/target selection table, non-vacuity table and exact
T1–T6 definition appendix. The definitions and contract scopes remain unchanged.
Refresh every moved source location by current declaration name, label the actual
M1 source snapshot, and update proof-status prose. Do not reuse M0 line numbers as
current references. The original Targets file remains byte-identical in this
snapshot; its full target definitions and quantifier order can be retained exactly.

Rule15 remains mandatory: BoolPRG brings evaluator/index-sampler witnesses;
LPNFamily requires the exact complete-draw sample_eff field; SPRG requires eval_eff,
idSamp_eff and sdSamp_eff. Raw bundles make no efficiency claim. T3 and T5 refer to
the same complete draw; T6 chooses one U/coin polynomial/core before every dimension
and prime schedule. Only target-conditioned assemblies produce the efficient new
primitive values. No Phase B computation, sampler construction or machine was added.

Non-vacuity remains explicit: PrimeSchedule has its Bertrand witness; LPN advice has
its Fin(kappaOf L+1) sentinel at zero/off-image dimensions; PRG advice has its explicit
default; exact draw types are nonempty; optional empty grids are total; scheduled
inverse maps have their declared off-image behavior. SP-W3 rules out zero/constant
seed witnesses in HasPolyStretch. No claim is made that BoolPRG assumptions or all
Targets are inhabited, or that later stretch/security proof obligations are finished.

## Current check evidence and final gates still required

The M0 report's 88 seals, 96 controls, 1036 constants, 948 public types, 511 theorem
prints, 146 direct holes, 265 transitive dependents, 670 declarations and old request
counts are HISTORICAL M0 results. They cannot be relabeled current M1 passes after
proof/import-environment changes. The new Basic owner must be included everywhere.

| Gate | M1 checkpoint requirement |
| --- | --- |
| Full owner checks | Bind all 23 current owners, including facades/Basic, to final source and import environment. |
| Frozen full types | Recollect all current types and compare every existing M0 full name/header; list the three new helper names separately. |
| Declaration census | Fresh decls2, stored constants/public types, clash scan and typed inventory; do not infer counts from +3 alone. |
| Axioms | Fresh full graph and public theorem prints; all 103 M1 filled/new bodies must avoid sorryAx. Enumerate remaining M2–M6 holes and transitive dependents accurately. |
| Rule10 | Regenerate collector order/masks/request counts for 23 owners. With four variants per owner, expect 92 seal modules if no additional owner lands; use actual generated counts as authority. |
| Paired controls | Regenerate coverage/counts and require all unsealed positives and exact one-failure sealed negatives. Do not assume M0's 96 remains the new count. |
| Source policy | Refresh explicit-unfold classification, lints/campaign deltas, widths/file sizes, permitted paths and mandatory-reuse disclosures. |
| Delivery | Bind final commit(s), replay/bundle/manifest checks, payload path set and push receipt to M1, preserving the archived M0 payload. |

The planned named-source delta is +3 (Basic2 and G4 support), so 673 would replace
M0's670 only if no other named declarations land. This is not a fresh decls2 or
kernel count; proof auxiliaries require a new census.

No fresh M1 global seal/census/replay claim is made by this draft. Existing owner
summaries and their source-hash matches are listed in snapshot.json; final Correctness,
Defs and Samplers summaries must be added after completion.

## Overlap-search evidence and harness corrections

Search outcomes are read individually; record_overlap.py's DIAGNOSTIC_FAILURE label
has several meanings. A clean apply? no-hit is different from a heartbeat timeout,
a failed goal elaboration, a rejected candidate attempt or a valid partial suggestion.
No failed or bounded search establishes the absence of an existing theorem. Partial
apply? goals and implicit sorry warnings never establish a closing proof.

The immutable saved-log snapshot covers {o['saved_search_count']} searches, all with
matching saved source/log hashes. Current per-log categories are:

'''
for k,v in o['semantic_counts'].items():body+=f'- {k}: {v}.\n'
body+='''
These counts are a dated audit snapshot while root continues searching, not final
campaign totals. overlap-log-review.tsv/json records every goal/mode and flags.
Failed intermediate candidate attempts are preserved as flags even when apply?
ultimately returns a valid partial rc0/errors0/sorry1 result. The seven originally
listed bounded diagnostic attempts in evidence/overlap/bounded-search-review.json
are a historical subset; newer Algebra/LPN timeout logs are classified individually.
The bounded diagnostic limit is 100000 heartbeats; owner proofs retain their separate
configured limit. Neither a timeout nor an API/header error is a completed no-hit.

The initial firstGood_none_iff and firstGood_some_flag overlap templates opened
BigOperators without an import defining that scope. Those four original exact/apply
records retain the unknown-namespace error and are not usable search evidence.
Root removes only the unnecessary scoped-open line when the goal has no sum/product
notation and reruns under distinct AlgebraV2 names. The fresh V2 suggestion
List.find?_some is an existing public API; only the new clean runtime record can be
counted. No owned theorem statement or proof algorithm changes for this harness fix.

The old BucketsSparse_sparseFactor_mul, BucketsSparse_sparseFactor_mul_of_card_le
and Algebra_oneSd_factors_mul probes each had HMul synthesis failures before the
tactic body, in both modes. These six historical records are retained as statement
elaboration failures. Fresh explicit-Matrix probes are recorded under the exact
BucketsSparseV2_sparseFactor_mul, BucketsSparseV2_sparseFactor_mul_of_card_le, and
AlgebraMatrixV2_oneSd_factors_mul names. Their exact runs complete without a closing
proof and their apply runs produce partial suggestions, with no harness errors;
supersession.tsv/json binds each old/new pair to its source/log hashes. SparseFactor's actual source proofs have their
separate standard-axiom owner summary; the faulty scratch harness does not refute
those proofs. Preserve all old records and link each to its exact superseding V2
record rather than deleting or silently relabeling it.

## Host/process deviations — retain both disclosures

The earlier whole-job two-subagent limit was exceeded when a child started a third
research descendant. Root interrupted that descendant and prohibited further
spawning/resumption. Reported activity was source reads, rg and temporary notes;
no Lean, Lake, cache, push or implementation-source mutation was reported. This is
based on task/activity reports, not an independent process-history audit. Duration
was not established and must not be called brief. The exact disclosure is retained
in evidence/host/team-limit-correction.json and the archived M0 report.

During M1, root also violated this job's one-Lean-at-a-time rule by overlapping the
Params_B_pos apply search with the step029 owner check. The recorded cause is that
only exec_command.output was printed, discarding an ongoing session_id, then an owner
check was launched before the search completed. evidence/host/search-process-correction.json
records search runner93880/wrapper93883/child93887 and owner wrapper93983, with a
confirmed overlap during 2026-11-18T15:07:45Z–15:07:48Z. Root sent SIGTERM only to the
recorded own child; the search wrapper release is recorded at15:08:34Z. Do not infer
unrecorded process history or characterize the total overlap duration beyond these
observations. The correction is to preserve full tool/session metadata, poll every
running session, bound diagnostic searches, and launch no further Lean until the
existing runner exits. This is separate from the all-jobs host cap and from the
subagent-count breach. Do not carry forward an unqualified whole-job seriality claim
or M0-only slot-summary maximum as if it covered M1.

The M0 source-PDF verification, delayed memory preflight and tool-provenance records
remain historical facts. No PDF is copied into source/evidence delivery. Root retains
the pinned wrapper and LEAN_SLOT_TAG=io-sprg. This draft performs only source/evidence
reads and writes temporary report files; it runs no Lean, git, cache or subprocess.

## Before promoting this draft

Rebind the final M1 head, refresh this source/log snapshot, finish all mandatory
lemmas, and replace every PENDING gate with its current source/environment-bound
evidence. Re-render/review the carried tables, then package a distinct M1 checkpoint.
Keep evidence/checkpoints/M0/REPORT.md unchanged. Do not execute report_current.py:
it hardcodes M0 hashes, owner inputs, 146-hole counts and historical gates.
'''
(b/'REPORT-M1.DRAFT.md').write_text(body)
print('Rendered unsigned M1 draft; no evidence/REPORT.md write.')
