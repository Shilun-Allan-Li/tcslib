# LWE/SIS construction campaign

Scope, sources, parameter decisions, directories and gates are in
[LatticeCryptographyPlan.md](../../LatticeCryptographyPlan.md).

## Current checkpoint

All five scoped gates pass 0/0/0/3, including the construction-core proof
report supplied as a user paste. All 31 core obligations are proved, with 263
owned constants free of sorryAx. Their code and records stay fixed on #237;
source-policy and relevant landing checks remain open for #236/#237.

The next isolated adapter draft is now checked in `tcslib-lwe-sis-adapters`,
branch `cryptography/lwe-sis-adapter-statements`, source
`6eec97be8f54d9990340900a5595dab32fb477f5`. It has 20 declarations and 14
explicitly admitted obligations; only its three complete defining equations
are proved. A fresh 93-module sweep passes; all 263 old constants are unchanged,
and nine consumed machine contracts have only standard axioms. Its statement
audit is dispatched to Codex. Draft PR
[#238](https://github.com/Shilun-Allan-Li/tcslib/pull/238) and exchange input
`a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4` are remotely verified; findings
now pass 0/0/0/3. Only the 14 audited theorem bodies may be filled next;
definitions/signatures and issued review inputs remain frozen.

See `gates/04-encoding-adapters/` for the current review packet and
`progress.md` for the campaign pulse. The one Encoding facade edit is in a
separate commit. Shared owner APIs, probability readers, source registry and
pins remain unchanged. Reference validation/ingestion/matching and the eventual
machine/primitive bridges remain open.

The central integration branch is `cryptography/lwe-sis-constructions`. Audited
Lean changes go through PRs into that branch for the user's approval and merge.
The active draft is `cryptography/lwe-sis-adapter-statements` in the separate
`tcslib-lwe-sis-adapters` worktree. Its audited dependencies are #236 and #237;
both existing PRs' central targets are remotely verified.

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

Active worktree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-adapters`.
Draft branch: `cryptography/lwe-sis-adapter-statements`.
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
pass, including the construction-core proof gate. The new adapter statement
gate, source ingestion/matching and relevant integration checks remain open.
The user approves and merges PRs.**
