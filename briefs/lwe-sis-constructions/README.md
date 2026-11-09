# LWE/SIS construction campaign

Scope, sources, parameter decisions, directories and gates are in
[LatticeCryptographyPlan.md](../../LatticeCryptographyPlan.md).

## Current checkpoint

The construction-core statement audit passes 0/0/0/3. Its verbatim findings and
separate dispositions are under `audits/`. All 31 approved obligations are now
proved at `690217cc1aaefe411158808a8b0797fd887a8abc`, on existing PR #237.
All definitions/signatures and the 62 source declarations are unchanged.

The fresh serial 68-module sweep passes with zero owned admissions and the same
17 inherited warnings. All 263 owned constants use only standard axioms, with
no sorryAx; seven compiler auxiliaries are explicitly inventoried. Freeze and
style checks pass. `fills/01-construction-core/` contains the evidence, report
and proof-audit handoff. The user has dispatched that audit; GitHub verifies
the published draft and immutable exchange input. The returned proof audit now
passes 0/0/0/3; its pasted report is preserved verbatim under `audits/`, with
separate resolutions and an intake receipt. No proof correction is required.

Independent source and machine-adapter preparation is under `continuation/`.
Raw local PDF extraction is complete, but validation/matching and the proposed
two-tag registry change remain unexecuted. Source-policy and machine/primitive
bridge obligations remain open. The new `continuation/proof-audit/` records
a nine-page visual source comparison, concrete arithmetic/sampling reuse, and
PKE preflight. No additional external job is dispatched by that preparation.

The central integration branch is `cryptography/lwe-sis-constructions`. Audited
Lean changes go through PRs into that branch for the user's approval and merge.
The active draft is `cryptography/lwe-sis-phase1-statements` in the separate
`tcslib-lwe-sis-phase1` worktree. It depends on audited PR #236; both PRs' central
targets are remotely verified.

The construction-core statement draft contains eight new mathematical modules,
62 source declarations with all 31 former admissions filled: sample schedules, modular
parsers, bit decoding, direct Regev symmetric encryption and its concrete
security bound, and SIS hashing/collision bounds with a dyadic profile. A fresh
68-module sweep passes. The statement gate passes;
the efficient machines and existing primitive bridges remain open.
See `gates/02-construction-core/` for the statement gate and
`fills/01-construction-core/` for the current proof handoff.

The phase-0 statement audit passed with 0 blockers, 0 majors, 0 minors and 3 notes.
The report is retained verbatim under `audits/lwe-sis-phase0-findings.md`, with its
dispositions in `audits/lwe-sis-phase0-resolutions.md`.

The representation-proof audit also passed with 0 blockers, 0 majors, 0 minors
and the same 3 continuing notes. Its verbatim report is
`audits/lwe-sis-encoding-proofs-findings.md`; its gate closure and retained
obligations are in `audits/lwe-sis-encoding-proofs-resolutions.md`. No Lean repair
was required. Maintainer intake reverified all 63 frozen source files and the
current, historical and exchange checksums; it did not rerun native checks.

All 14 audited representation lemmas are now proved at
`893e921bf2afeca293be9da9d495613bb1486796`: modular vector/matrix lengths and
injectivity, LWE/SIS challenge lengths and faithfulness, signed SIS decoding completeness,
and polynomial input/output bounds. The 61 public declarations and their signatures,
definition/instance bodies, attributes and namespaces are unchanged. No helper was added.

The public hypotheses remain `TCSlib.Cryptography.LWE.DLWEAssumption` and
`TCSlib.Cryptography.SIS.SISAssumption`. They define hardness propositions; no hardness
axiom, efficient sampler or primitive-security endpoint follows from these propositions alone.

## Foundation verification (historical)

A fresh serial 55-module dependency sweep through `scripts/lean_check_tree.sh` passes
with zero errors, zero new admissions and the same 17 inherited warnings. It uses a newly
created own olean tree and is not a whole-library root check.

All 61 source declarations and all 166 elaborated constants use only standard axioms,
with no `sorryAx`. Two new compiler-generated congruence constants are inventoried.
Source signatures and all other frozen code are checked by `verify_freeze.py`.
Style reports zero FAIL and the same two acronym-reader false positives accepted by the
statement audit. No linter edit or reader rename was made.

Foundation proof evidence is under `fills/00-encodings/evidence/`. Historical statement
evidence under `gates/00-foundations/evidence/` remains unchanged and records 14 admissions
at its earlier freeze. Independent finite-model calculations remain supporting checks;
they do not execute Lean or prove security.

## Ownership and publication

Active worktree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-phase1`.
Draft branch: `cryptography/lwe-sis-phase1-statements`.
Central PR target: `cryptography/lwe-sis-constructions`.
Audited dependency: `0769cba3e44c56700349f954190fc99d9e622270` (PR #236).
Phase-1 Lean/root freeze: `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`.
The original campaign context and older source/audit identities remain historical.

All Lean updates go through a user-approved PR. The foundation's three root imports
remain isolated in export commit `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`.
The next phase adds two root imports and small Encoding/LWE facade additions in
its separate export commit. Those are the only existing-file Lean changes relative
to the audited dependency. Existing owner APIs, pins, other campaigns' records and
other maintainers' checkouts are unchanged.
Builds use only the own pinned packages and scratch objects; root native/cache jobs are serial.

The user selected and dispatched Codex for proof review. Inputs were published under
`lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/` on the orphan exchange;
the exact audited exchange commit is
`ebe777ba3bf904f6a6909aaf8b931fcb0c53f358`. Codex returned Markdown in chat.
The separate sparse publisher clone changes only this namespace, leaving the shared
exchange checkout, index and original inbox reports alone. The previous statement
input is published at exchange `09d1456efacded71850c84497db5c8d1f65ab0a0`.

Draft PR [#236](https://github.com/Shilun-Allan-Li/tcslib/pull/236) is published
from `cryptography/lwe-sis-encoding-proofs`, with audit-intake head
`0769cba3e44c56700349f954190fc99d9e622270`. The user has selected the central
branch as its target, and client retargeting is now verified. The connector's
earlier HTTP 403 remains a historical preparation record. The observed central ref is
`2c37f3f486822a52f4a9e337c6b742e995ebb118`. Client publication resolved the earlier
connector/DNS block; historical preparation records remain unchanged. Source PDF
acquisition is now complete for Pei16/Wu24, with exact hashes and version checks;
ingestion/source matching, landing checks and future sampler/profile/machine
obligations remain open under N01–N03.

**Not yet clear to merge — the foundation and construction-core statement gates
pass, including the construction-core proof gate. Source ingestion/matching and
relevant integration checks remain open. The user approves and merges PRs.**
