# M1 checkpoint report update plan — no REPORT overwrite

All files here are temporary drafts/read-only helpers. Do not execute
`evidence/tools/report_current.py`: it invokes git, hardcodes the 1a941 review
snapshot/M0 owners/gate locations, asserts M0 source hashes, and emits stale
146-hole/22-owner census text. This preparation did not execute that tool, any
Lean/git/cache command, or any subagent operation. It did not modify evidence/REPORT.md.

The root should finish the following complete M1 list before sign-off:

- Raw LPN3, Degree24, Params14, Encoding17, Buckets7, SparseFactor5, Polys10.
- Correctness18, plus the specific G4_seed_allOutputs helper.
- SPRG.Raw.HasComplexityEff.hasComplexity in Defs.
- Params.primeWidthBound in Samplers.
- Both new Basic fixed-width tagged-list theorems.

This is 100 original bodies plus three new theorem-only helpers, total103, including
Encoding17's early support work. If no other proof is filled, 46 original direct
holes remain. M6 supporting encodings are done early; M6 links and Phase B target
truth remain separate. Do not omit the two one-line-looking Defs/Samplers obligations
from the milestone or their final axiom/owner checks.

Refresh the SAFE temporary snapshots after root finishes. Each script reads source
and evidence and writes only this /private/tmp directory; none runs a subprocess:

    python3 /private/tmp/io-sprg-proof-notes/M1CheckpointDraft/snapshot_readonly.py
    python3 /private/tmp/io-sprg-proof-notes/M1CheckpointDraft/classify_overlap_readonly.py
    python3 /private/tmp/io-sprg-proof-notes/M1CheckpointDraft/render_draft_readonly.py

Keep these dependent refresh operations sequential. A source file changing during
the snapshot is reported explicitly; rerun once the source is stable. Static sorry
counts are useful crosschecks, not typed or transitive axiom evidence. The last
recorded progress commit is not inferred to be the final HEAD; root binds the final
commit separately through its authorized workflow.

The source plan currently has23 owners: Basic is added to M0's22. The future LPN
Defs/Encoding/Transport/Hop split is proposed only and must NOT be counted as landed
here. Include Basic before Encoding in the actual collector/module order and include
its theorem expressions and imports in every declaration/seal/census gate. If the
scope grows before checkpoint, regenerate all counts from the actual owner list.

Named-source delta expected from the planned work is +3 (Basic2 and G4 seed support),
with every existing full type/definition unchanged. M0's670 named-source additions
would therefore become673 if there are no other named additions; at the current
snapshot, only Basic2 is present. This is an expectation, NOT a new decls2 result.
Stored-constant/public-type/public-theorem counts can change through proof auxiliaries
and must come from fresh collectors, not arithmetic on M0's1036/948/511 counts.

## Report sections to retain and sections to replace

carry-forward-tables.tsv gives the exact M0 archive section anchors, reusable content
and required updates. Preserve the mathematical content of fidelity, Rule15,
non-vacuity, target-field selection and exact target definitions. Their existing
contracts do not change just because proofs are now filled. Target truth remains
unproved. Update the snapshot labels and source positions by DECLARATION IDENTITY,
not blind offsets or a sequence matcher pinned to an old review revision. Ambiguous
structure-field references need a manual anchor in the current owning structure.

Add a Basic theorem-glue row and the specific G4 support-helper row to the exhaustive
source/declaration inventory. New helpers are mathematical glue, not paper claims or
new algorithms. Keep private fixed-width overlap disclosed and cite public reuse.
Do not replace the mandatory phase-B notice by proof-status prose about conditional
assembly bridges. Keep rational delta, prime-before-input quantifiers, same complete
draw T3/T5 and one U/c/f before all schedules in T6 exactly as frozen.

Rewrite the report opening, current head/commits, milestone table, source-size counts,
all gates, proof-obligation inventory and overlap status. Historical M0 seals/counts
must stay labelled M0. Recompute the current full graph and #print axioms so all103
newly filled/theorem-added bodies are standard-only, while remaining later-phase
holes and their actual transitive dependents are reported precisely.

The final report must cite fresh current-source/import-environment owner passes,
full types, decls2, clash, lint/campaign deltas, widths, explicit unfolding, collector,
four seal variants and paired controls. Four variants ×23 current owners suggests92
seal modules; actual generated plans decide the count. Paired-control counts may
change with term-use coverage: do not blindly reuse96. Rebind every source/log/olean
environment and include Basic. Final replay, bundle/manifests, payload source hashes,
M1 checkpoint and exchange/push metadata are root-only final delivery work.

## Search audit and superseding records

Do not treat DIAGNOSTIC_FAILURE as a mathematical outcome. The safe classifier
reviews immutable saved logs individually, verifies their source/log hashes, and
keeps all flags. It distinguishes CLOSED, valid partial with implicit sorry,
completed exact failure, clean apply no-hit, bounded timeout, header/API error, and
unresolved diagnostic. A failed intermediate candidate attempt can appear in a log
whose final result is a valid partial; that does not make it a closing proof or a
fatal final elaboration failure. A timeout at source line1 is still a timeout, not
evidence that the goal header itself was malformed.

The original seven timeout rows in bounded-search-review.json are not the entire
current set. Refresh per-log totals from actual saved immutable records. Clean
no-hits are unsuccessful finite searches, not proofs that no reusable theorem
exists. Bounded searches cannot support either global absence or proof success.

Preserve and explicitly supersede the following OLD harness records:

- Algebra_firstGood_none_iff exact/apply -> AlgebraV2_firstGood_none_iff exact/apply.
- Algebra_firstGood_some_flag exact/apply -> AlgebraV2_firstGood_some_flag exact/apply.
- BucketsSparse_sparseFactor_mul exact/apply -> BucketsSparseV2_sparseFactor_mul.
- BucketsSparse_sparseFactor_mul_of_card_le exact/apply ->
  BucketsSparseV2_sparseFactor_mul_of_card_le.
- Algebra_oneSd_factors_mul exact/apply -> AlgebraMatrixV2_oneSd_factors_mul.

All five exact-name pairs are now recorded, with both modes and source/log hashes,
in supersession.tsv/json. The fresh Matrix exact runs complete without closing the
goal; the apply runs are valid partial suggestions, not closing proofs.

The first four old runs have unknown BigOperators namespace errors. Remove the
unnecessary scoped-open command for goals without sum/product notation; do not add
a heavy import for unused notation. The six old matrix-factor runs have HMul synthesis
errors in the goal statement, fixed by actual Matrix type annotations. Neither
harness repair changes an owned source theorem. Actual SparseFactor source proofs
have their independent standard11 axiom summary. The new clean List.find?_some
suggestion is existing public reuse, counted only from the fresh V2 run. Do not
delete old failure evidence or silently rewrite its original automatic label.

## Mandatory process disclosures

Carry forward the WHOLE-JOB subagent limit breach exactly: third research descendant,
interrupted by root, no further spawn/resume, activity only reported by parent task
context, no independently established duration or process audit. Never call it
brief. Cite evidence/host/team-limit-correction.json and the archived M0 report.

Also disclose evidence/host/search-process-correction.json: root lost the ongoing
exec session_id by retaining only .output, then overlapped Params_B_pos apply with
step029's owner check. Recorded confirmed overlap includes15:07:45–15:07:48UTC;
recorded child-only SIGTERM and wrapper release at15:08:34UTC are facts, not a basis
for inventing the rest of the process history. Preserve full tool metadata, poll
all active sessions and launch no new Lean before runner exit. Distinguish this
per-job one-Lean violation from the global three-process host cap and the subagent
count limit. Do not repeat the old unqualified seriality or max-one wrapper claim
as a whole-history M1 claim. Historical M0 preflight/PDF/provenance stays historical.

## Promotion

The generated REPORT-M1.DRAFT.md is deliberately unsigned. Before replacing the
active report, fill its final M1 head and exact gate evidence; re-render/update its
remaining/PENDING statuses and check that every source and log reference resolves.
Preserve evidence/checkpoints/M0/REPORT.md and its payload. Package M1 separately
and continue later milestone work; no final whole-job completion claim is warranted.
