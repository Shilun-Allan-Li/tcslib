# Real canonical column law: completed candidate assembly

Status: FULL SCRATCH CANDIDATE, not natively elaborated/sealed/axiom-checked. No Lean/lake/
build/Git/live edit/process operation/extra agent/native search was run by this child.
Root owns all native integration and checks.

Candidate: DlinRealColumnGap.lean.inc. Exactly one tactic block, no term sorry/admit/axiom/
native_decide, <=100 columns. Seven local tactic goals retain the same seven swap/bullet
branches as the earlier skeleton; only native elaboration can verify they all discharge.
The exact theorem header and docstring were byte-compared with CURRENT LIVE ColumnLaws.lean
and are identical. The prior DlinRealColumnGap.skeleton.lean.inc remains archived unchanged.

## Only change from the prior skeleton

The sole hSurj term sorry is replaced with the TERM call
  fun ab hab => dlin_base_transpose_mulVec_surjective (K := K) (ab 0) (ab 1) hab.
Its step comment now describes reuse instead of a pending header request. A textual inverse
replacement confirms ALL OTHER skeleton text is identical. No geometry, matrix-image,
probability or counting proof is added or repeated in this invocation. No public/runtime
algorithm or new helper is defined. The existing local A is the let-bound literal from
this theorem's own statement, so using it at the helper call requires no foreign unfolding.

## Dependencies / honest status

- Root reports both FiniteLinear helper proofs native PASS and completely admission-free.
- The dlin_base_transpose_mulVec_surjective full candidate has been delivered separately
  (DlinBaseSurjective.lean.inc); root's native integration/check is QUEUED, not yet claimed
  PASS by this child. This completed real-law candidate depends on that named theorem.
- All other range/transpose/image/coordinate-mass/averaging code is retained exactly from
  the earlier inspected skeleton. Its detailed static reuse sources and candidate risks
  remain documented in DlinRealColumnGap-SKELETON.md. In particular no local Diagonal
  hBadMass counting is copied: OneWay.uprob_pi_forall and public singleton readers are used.
- Root's valid main/helper native reuse probes found no complete preexisting proof and no
  target typing errors. They do NOT certify this candidate proof. This document asserts
  no main PASS or standard-only dependency chain until root completes native checks.
- The random-column law is unchanged. The frozen direct correction is still 4d/p and no
  dlinMatrixSlack term is introduced.

## Actual read/search this invocation

rg for dlin_base_transpose_mulVec_surjective / dlin_real_column_gap_le / have hSurj in the
live MatrixDH directory and this scratch directory found the exact current helper/header
and earlier skeleton. Read their exact headers and hSurj context, the current main live
header/prose for byte comparison, and root's DlinBaseSurjectivityExact.lean.txt target.
Located both valid search result inventories under evidence/search/dlin-column-laws/run
and evidence/search/dlin-base-surjectivity/run. No fresh native exact?/apply? call was made.
There is no new helper to search: this is term assembly from the already-probed geometry.
