# LWE/SIS construction campaign

Scope, sources, parameter decisions, directories and gates are in
[LatticeCryptographyPlan.md](../../LatticeCryptographyPlan.md).

## Current checkpoint

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
axiom, efficient sampler or primitive construction/security theorem is asserted.

## Verification

A fresh serial 55-module dependency sweep through `scripts/lean_check_tree.sh` passes
with zero errors, zero new admissions and the same 17 inherited warnings. It uses a newly
created own olean tree and is not a whole-library root check.

All 61 source declarations and all 166 elaborated constants use only standard axioms,
with no `sorryAx`. Two new compiler-generated congruence constants are inventoried.
Source signatures and all other frozen code are checked by `verify_freeze.py`.
Style reports zero FAIL and the same two acronym-reader false positives accepted by the
statement audit. No linter edit or reader rename was made.

Current proof evidence is under `fills/00-encodings/evidence/`. Historical statement
evidence under `gates/00-foundations/evidence/` remains unchanged and records 14 admissions
at its earlier freeze. Independent finite-model calculations remain supporting checks;
they do not execute Lean or prove security.

## Ownership and publication

Worktree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-crypto-parallel-kickoff`.
Current PR branch: `cryptography/lwe-sis-encoding-proofs`.
Earlier published topic snapshot: `cryptography/lwe-sis-constructions` (left unchanged).
Baseline: `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49`.
PR target: `cryptography/pass-shelat-ch2-4`.

All Lean updates go through a user-approved PR. The only existing shared-file overlap
is still three root imports, isolated in export commit
`4364d0e0fe9accd649b6acb4751e8684aa93ad1e`. This fill adds no root edit. Existing
owner APIs, pins, other campaigns' records and other maintainers' checkouts are unchanged.
Builds use only the own pinned packages and scratch objects; root native/cache jobs are serial.

The user selected and dispatched Codex for proof review. Inputs were published under
`lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/` on the orphan exchange;
the exact audited exchange commit is
`ebe777ba3bf904f6a6909aaf8b931fcb0c53f358`. Codex returned Markdown in chat.
The separate sparse publisher clone changes only this namespace, leaving the shared
exchange checkout, index and original inbox reports alone. The previous statement
input is published at exchange `09d1456efacded71850c84497db5c8d1f65ab0a0`.

Draft PR [#236](https://github.com/Shilun-Allan-Li/tcslib/pull/236) is published
from `cryptography/lwe-sis-encoding-proofs` to the campaign target; its head before
this records-only intake is `aaf4d1d3ea2e5113b6f53c3fedd9b5d47e852de1`.
The earlier `cryptography/lwe-sis-constructions` ref remains unchanged at
`2c37f3f486822a52f4a9e337c6b742e995ebb118`. Client publication resolved the earlier
connector/DNS block; historical preparation records remain unchanged. Source PDF
archival/ingestion, landing checks and future sampler/profile/machine obligations
remain open under N01–N03. Live source checks do not close archival provenance.

**Not yet clear to merge — statement and representation-proof gates pass; source
archival and relevant integration checks remain open. The user approves merges.**
