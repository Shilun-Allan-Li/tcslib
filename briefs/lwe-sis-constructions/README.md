# LWE/SIS construction campaign

Scope, sources, parameter decisions, directories and gates are in
[LatticeCryptographyPlan.md](../../LatticeCryptographyPlan.md).

## Current checkpoint

The phase-0 statement audit passed with 0 blockers, 0 majors, 0 minors and 3 notes.
The report is retained verbatim under `audits/lwe-sis-phase0-findings.md`, with its
dispositions in `audits/lwe-sis-phase0-resolutions.md`.

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

The user freshly selected Codex for proof review. Inputs are prepared under
`lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/` on the orphan exchange;
Codex returns Markdown in chat and the user dispatches the job. The separate sparse
publisher clone changes only this namespace, leaving the shared exchange checkout,
index and original inbox report alone. The previous statement input is published at
exchange `09d1456efacded71850c84497db5c8d1f65ab0a0`.

The remote topic branch currently contains the earlier foundation snapshot. The proof
update awaits client publication: shell GitHub access fails DNS, and connector PR creation
returns HTTP 403. No PR or completed proof-review dispatch is claimed. Source PDF
archival/ingestion and the future sampler/profile/machine obligations remain open under
N01–N03. Live source checks do not close archival provenance.

**Not yet clear to merge — statements and all representation proofs pass; external
proof review, source archival and user-controlled integration remain open.**
