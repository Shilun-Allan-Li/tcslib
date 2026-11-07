# LWE/SIS construction campaign

Approved scope, directories, source anchors, parameter decisions and gates are in
[LatticeCryptographyPlan.md](../../LatticeCryptographyPlan.md).

## Current checkpoint

Phase 0 contains finite-seed scalar noise, numeric LWE/SIS parameters, a common-secret
LWE sample map, the integer SIS relation, concrete experiments, binary encodings and
asymptotic families with polynomial representation budgets. The public hypotheses are
`TCSlib.Cryptography.LWE.DLWEAssumption` and
`TCSlib.Cryptography.SIS.SISAssumption`. Every new public definition has an owner-side
reader. These define hypotheses; they do not assert axioms or prove hardness.

The 13 new Lean files comprise ten mathematical modules and three facades. At source
they introduce 61 public declarations: 19 definitions, five structures, 35 theorems and
two anonymous instances. Fourteen representation statements remain admitted, with
sketches beside them. Other proof terms are defining equations, one parser case reader
and the nonzero-modulus instances. All are part of the review surface. No construction
security proof has started.

## Verification

A fresh serial sweep checked the facades' complete 55-module transitive TCSlib dependency
tree through `scripts/lean_check_tree.sh`, with zero errors. Both renamed assumption
modules and both facades then passed rechecks. This scoped check is not a whole-library
check of `TCSlib.lean`. Logs contain 14 new and 17 inherited admission warnings.

The final probe imports all three facades, prints axioms for all 61 source declarations
and enumerates their modules' elaborated constants. Neither assumption nor its reader
depends on `sorryAx`. Exact results, style logs and order are under
`gates/00-foundations/evidence/`. Admitted statements are not completed proofs.
Style reports zero FAIL and two acronym-reader heuristic WARNs; the actual `_iff`
readers follow the existing RSA/DDH convention. No zero-WARN claim is made.

`check_finite_models.py` and `finite-model-results.json` record independent exact
small-instance calculations. They check conventions and boundaries; they do not execute
the Lean definitions or prove security. `phase0-source-review.md` records internal
review, which does not close the external gate.

## Isolation and delivery

Worktree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-crypto-parallel-kickoff`.
Branch: `cryptography/lwe-sis-constructions`.
Implementation baseline: `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49`.
PR target: `cryptography/pass-shelat-ch2-4`.

The only existing shared-file change is three root imports, kept in a separate commit.
Existing cryptography APIs, dependency pins, Pass--Shelat records, other worktrees and
exchange files are unchanged. All package/cache/build work is isolated here. Selected
official pinned Mathlib archives were extracted into the own package tree; no other
chat's TCSlib scratch objects were borrowed. The approved two-job increase lifted the
earlier scheduling hold. Root ran native/cache work serially.

Shell GitHub access fails DNS; own remote branch creation through the connector fails
HTTP 403, `Resource not accessible by integration`. No published branch or PR is claimed.
No external audit/fill job has been dispatched or exchange namespace selected. Source
PDFs were inspected through browsing; exact PDF archival, ingestion and proofmatch
remain open and are disclosed in the review packet.

The user selected Codex for the external phase-0 audit. The selected-worker kickoff is
`gates/00-foundations/dispatch-codex.md`; the already delivered round-1 ZIP and pack remain
unchanged. The user dispatches the audit and may publish only this own PR branch. No
campaign branch push or merge is authorized by that publication.

**Not yet clear to merge — the external foundation gate and source archival are pending;
14 representation proof obligations remain admitted.**
