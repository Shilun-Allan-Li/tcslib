# LWE/SIS construction campaign

Scope, sources, parameter decisions, directories and gates are in
[LatticeCryptographyPlan.md](../../LatticeCryptographyPlan.md).

## Current checkpoint

**Ten scoped gates pass.** The independent 31-proof Codex review passes
0 blockers/0 majors/1 documentation minor/4 notes at source
`f293b63200ee3c6de6e709925f67c4d60fdc7b4a` and exchange
`8efc0e669ed3ed004616c4aab81317ebf5fa17e6`, on existing draft PR #250.
Its F02 flat-generator overview is corrected separately at
`af54d28f6d412bc56844e7371e2b0b9b394c494c`, with identical code and a passing
module/style check. No mathematical repair is required. Seventy owned admissions
and all N01–N04 obligations remain. No merge is clear yet.

The source-policy job for the earlier #236–#239 stack has returned a partial
delivery at exchange `a4e19bd3cf029b9bf5fb2e53989ddc0d61006ac1`. Its local intake
verifies 58 delivery checksums, 191 frozen source/record blobs, four primary
assets and 703 typed matching records. All 161 declarations have dispositions;
59 proposed matches cite seven already-repaired pages. They remain unapproved.

Following the user's feedback, bulk PDF-to-Markdown transcription is postponed.
Review now targets the consumed PDF passages, adaptations and matching records;
the 186 other unvalidated transcription pages are not missing Lean work or an
additional landing requirement. See `continuation/landing-source-policy/SCOPED-REVIEW.md`
and its `intake-r1/` records. Applicable scoped reference integration and landing
checks remain. Later #250/PW10 source work stays separate. No shared registry,
blueprint/dataset or code is changed by this intake or scope decision.

The current code remains on the same isolated #250 worktree/branch. The 31 fills,
589-constant axiom inventory and fresh 144-module scope pass; all 575 earlier
elaborated types agree, with two compiler-origin changes disclosed. Full primitive
interfaces, efficient family sampling/schedules and final CPA/CCA2 integration
remain separate. The pending readers and loop catalogue/host-gate routes stay paused.

## Audited dependency stack

The dyadic arithmetic dependency is proved on PR #239's branch,
`cryptography/lwe-sis-dyadic-arithmetic`, in `tcslib-lwe-sis-dyadic-arithmetic`.
Filled source `ec72ed773a690c17ac253707350935cc9e0acb34` discharges all twelve
scalar obligations with the same eighteen declarations. A fresh 94-module sweep
passes; all 302 owned constants and sixteen backing contracts use only standard
axioms. Its statement audit passes 0/0/0/3 at exchange
`1ac4e2e45df94d0b5f20259218d067843458c770`. Its separate proof audit now passes
0/0/0/3 at exchange `083448cef9229dc95b96ef45686ce7f3768992ab`. See
`fills/03-dyadic-arithmetic/` and historical `gates/06-dyadic-arithmetic/`.

All eight scoped gates pass 0/0/0/3, including the construction-core proof
report supplied as a user paste. All 31 core obligations are proved, with 263
owned constants free of sorryAx. Their code and records stay fixed on #237;
source-policy and relevant landing checks remain open for #236/#237.

The isolated adapter draft is now proved in `tcslib-lwe-sis-adapters`,
branch `cryptography/lwe-sis-adapter-statements`, filled source
`b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e`. All 14 audited obligations are
filled, with the same 20 source declarations. A fresh 93-module sweep passes;
all 284 owned constants and nine consumed machine contracts have only standard
axioms. All 263 earlier constants retain exact identity/axiom sets, with one new
compiler arithmetic auxiliary disclosed. Its statement audit passes 0/0/0/3.
Draft PR
[#238](https://github.com/Shilun-Allan-Li/tcslib/pull/238) and exchange input
`a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4` are remotely verified; findings
pass 0/0/0/3. The subsequent Codex proof audit also passes 0/0/0/3 at exchange
`228c265d642013da76afa6cec976eaf11a8eb1b9`. Its report is preserved verbatim
from the user paste; definitions/signatures and issued inputs remain frozen.

See `fills/02-encoding-adapters/` for the current proof-review preparation and
`gates/04-encoding-adapters/` for the passing statement gate;
`progress.md` for the campaign pulse. The one Encoding facade edit is in a
separate commit. Shared owner APIs, probability readers, source registry and
pins remain unchanged. Reference validation/ingestion/matching and the eventual
machine/primitive bridges remain open.

The central integration branch is `cryptography/lwe-sis-constructions`. Audited
Lean changes go through PRs into that branch for the user's approval and merge.
The current draft is `cryptography/lwe-sis-construction-statements` in the separate
`tcslib-lwe-sis-construction-statements` worktree. Its audited dependencies are
#236/#237/#238/#239, stacked through
`307cfdd1d6cadfda2ae9cca5367705ad770c5f42`. Integration of those PRs remains
user-controlled; this draft does not merge them into the central branch.

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

Active worktree: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-construction-statements`.
Draft branch: `cryptography/lwe-sis-construction-statements`.
Central PR target: `cryptography/lwe-sis-constructions`.
Audited stack and intake: `307cfdd1d6cadfda2ae9cca5367705ad770c5f42` (PRs #236–#239).
Historical foundation dependency: `0769cba3e44c56700349f954190fc99d9e622270` (PR #236).
Phase-1 Lean/root freeze: `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`.
The original campaign context and older source/audit identities remain historical.

All Lean updates go through a user-approved PR. The foundation's three root imports
remain isolated in export commit `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`.
The combined phase changes six existing root/facade export files in its separate
export commit, as enumerated in `gates/08-construction-statements/REPORT.md`.
Those are the only existing-file Lean changes relative to its audited stack.
Existing owner APIs, pins, other campaigns' records and
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

**Not yet clear to merge — ten scoped gates pass. Source-policy closure and
exact-target landing checks remain for the earlier PRs; #250 also retains
seventy admissions, shared-owner holds and user-controlled integration.**
