# Campaign pulse

The combined statement and independent 31-proof audits each pass **0 blockers,
0 majors, 1 documentation minor and 4 notes** on draft
[#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250). Both documentation
minors are corrected separately and checked. The combined Gate 11 audit also passes both scopes.

The audited independent proof fill completes **31 obligations in seven modules** at
`f293b63200ee3c6de6e709925f67c4d60fdc7b4a`. The
same isolated branch/worktree is used; no additional PR branch is created.
The fills are published and their combined Codex proof audit passes. Its sole
F02 overview repair is checked at
`af54d28f6d412bc56844e7371e2b0b9b394c494c`. The user
dispatches source work, approves matching and approves all merges.

The six Regev hybrid support proofs pass their audit with 0 blockers, 0 majors,
0 minors and 4 continuing notes. The checked source is
`8c6b23f5b69260acb66cc99e322a81c4c79f51bb`, leaving **64 owned admissions**.
The fresh 144-module sweep records zero errors and the same 17 inherited
admission warnings. All six fills use only standard axioms, with the 589-constant
inventory reconciled. See [the proof report](fills/05-regev-hybrids/REPORT.md).

The user approved the two shared probability readers on [draft #255](https://github.com/Shilun-Allan-Li/tcslib/pull/255).
With those readers, six more proofs complete the finite fixed-bit Regev security
bound and leave **58 owned admissions**. Both scopes pass with zero blockers, majors, and minors. The auditor reran both
serial closures and reproduced both axiom probes. See
[the Gate 11 findings](../../audits/lwe-sis-regev-statistical-proofs-findings.md).

| Part | Current progress | Remaining work |
|---|---|---|
| DLWE/SIS foundations and sampling | Foundations, exact dyadic laws, bit-noise probability/support/symmetry/mean and common-secret sampling/test laws proved and audited | Efficient uniform family samplers and schedules, source policy |
| Direct Regev symmetric encryption | Algorithms, bounded-error correctness and concrete two-DLWE bound proved and audited | Efficient implementations, uniform message bounds and final existing-game bridge |
| SIS collision-resistant hashing | Core hash/reduction/profile, strong extraction, raw evaluator and exact collision-to-SIS output proofs audited | Counted-loop efficiency, and the CRH interface under independent SIS hardness |
| Regev CPA PKE | Every-coin correctness and hybrid support audited. Statistical hybrid and final finite fixed-bit bound proved and audited | Efficiency, asymptotic bounds, and CPA interface |
| PRGs | All eleven structured/MSB/flat generator obligations proved and audited with complete seed budgets | Efficient family schedules and standard exact-seed asymptotic PRG integration |
| CCA2 PKE | Finite concealer hybrids, signed rounding, lossy image bound, and designated-branch cancellation audited. Anti-cyclic rank, injective-mode recovery and non-designated branch injectivity checked | Efficient all-but-one inversion, strong one-time signatures and CCA2 |

The earlier independent proof audit's fresh 144-module scoped sweep took 303.792
seconds with zero errors, seventy owned and seventeen inherited admission
warnings. Its axiom probe
records 53.149 seconds. All 31 selected targets and 48 backing contracts use only
standard axioms. Exactly the other seventy source obligations retain `sorryAx`.
The full inventory has 589 constants, including fourteen new compiler auxiliaries.
Two old congruence helpers have earlier originating modules, explicitly recorded;
all 575 previous elaborated level/type representations compare exactly. Style is
0 FAIL/2 unchanged WARN over 41 files; other native warnings match the statement
baseline. No whole-library root elaboration or complete security endpoint is claimed.

PRs #236 through #239 have merged into `cryptography/lwe-sis-constructions`.
The verified central tip is the #239 merge
`27f9ea89b72d84abaec8128f2abd826f24aaced4`. Local #250 integration commit
`6e230c9a518aadc30b1323a28be9ef96e5fd62c8` incorporates that exact target and
preserves the checked Lean tree and pins. Intake verified GitHub draft #250
at `b07abbb3b69a89b95fbc76c18ed0cf7bc13c638b` and the published Regev audit packet
at exchange `3be2879df1cb5d37fd7cd2275bb520598e8c41eb`.
Original statement source `17b2a282b545c6ebca3fccc88d518d18ae78f485` and exchange
`64e245b345d908d835030efede1c91312a4e6cce` remain immutable historical inputs.

## Regev hybrid support

The passed proof review covers the uniform hash difference, extraction error
budget, exact real-to-uniform-key DLWE hybrid, augmented-key bijection,
ciphertext identity, and doubled error budget.

The statistical proof fill uses `isUniversal_iff` and `hasMinEntropy_iff` from
the approved owner-side patch on #255. A one-line `omit` in the universality
reader removes the unused input `Fintype` instance found by Lean. The corrected
four-module owner check and the dependent replay on #250 pass. The random-bit
reader and counted-loop registry disposition remain separate holds for the
trapdoor and machine proofs.

The source-policy job at `continuation/landing-source-policy/` returned partial
work for the earlier #236–#239 stack, 161 declarations in 20 modules at
`ec72ed773a690c17ac253707350935cc9e0acb34`. All returned checksums, four original
assets, 191 frozen blobs and 703 typed matching records pass local intake. The
59 proposed matches in that delivery use seven already-repaired PDF pages.
The subsequent scoped approvals record 37 distinct attributions in
`landing/01-foundations/` and `landing/02-construction-core/`, inherited by
the merged adapter and scalar PRs.
The user asked to postpone unrelated transcription; the root has narrowed future
work to consumed source passages, accurate adaptation notes and reviewed matching.
Source review for #250's new claims remains open, including PW10 where consumed.

## SIS encoding and finite trapdoors

The new wave fills 40 audited obligations in nine modules at
`3bf1cb424b10abef3ae7a438c6b7d0e1916d0800`. The 144-module sweep passes with
zero errors. The 220 elaborated type comparisons agree with Gate 11, and all
40 proofs use only standard axioms. The 18 remaining admissions are listed
in the [proof report](fills/07-sis-trapdoor/REPORT.md). The scoped PW10 preflight
pins the author PDF and the consumed passages.

Gate 12 round one passed the mathematics and axiom checks for all 40 fills and
reproduced both native sweeps. It held on the duplicate subset-sum proof. The PW10 reference
ranges and overview are corrected in `d3bb52db5aaf249a35e83506371a3c86e76cb69a`.
The user approved the exact shared-owner patch. The repair at
`93dc88648f117877e42aaf58ba7b911c76a4b63a` places the common proof in `LWE.Basic`
and preserves both theorem signatures. The 144-module fresh sweep, axiom
probe, and all 220 elaborated type comparisons pass.
[Round two repair report](fills/07-sis-trapdoor/round2/REPORT.md)
[Gate 12 findings](../../audits/lwe-sis-trapdoor-proofs-findings.md) ·
[Exact proposed diff](fills/07-sis-trapdoor/intake-r1/proposed-binary-error-sum.patch)

PR #255 is merged. The live central tip is
`41aaf0a1acf29318fa8d741dadd9f5f585e43c93`. The merge preview preserves the
current #250 Lean tree, root, and pins.
[Reader landing record](https://github.com/Shilun-Allan-Li/tcslib/blob/6410ad6375afe46dcea23b882dcf7eab302fe78e/briefs/lwe-sis-constructions/prerequisites/01-probability-readers/LANDING.md)

Gate 12 round two **passes the 40-fill proof gate** with zero blockers, majors,
and minors. The independent replay reproduces all 144 module logs and both
probes. F01 and F02 are closed. Four continuing notes remain.
[Round two findings](../../audits/lwe-sis-trapdoor-proofs-r2-findings.md) ·
[Audit disposition](../../audits/lwe-sis-trapdoor-proofs-resolutions.md)

Intake verifies exchange `3d1d76833cf36a614559338dd31a2dc0459618d5`,
the exact patch, all 260 indexed attachments, and the merge preview.
[Verified intake](fills/07-sis-trapdoor/round2/review-intake.json)

## Anti-cyclic rank

Both rank proofs are checked at `75a4214dc098cd6c363d00c34f569bac23eb4555`, leaving 16
owned admissions. The affected closure and three probes pass. Of the 220
types, 216 match exactly and four have kernel-checked definitional equality. The existing power basis and cyclotomic result
use the same pinned Mathlib. This checkpoint enters the next combined
proof review. [Rank report](fills/08-anti-cyclic-rank/REPORT.md)

## Gadget and inversion

The approved shared reader is isolated at `2414fd3eae05c99474d1888609b01ac5989523a5`.
Seven further fills at `713093c36ac66f7e56e9354581f0bb3f59772341` prove positional gadget evaluation,
injective-mode recovery and non-designated branch injectivity. The fresh
144-module sweep passes and leaves nine counted-loop and CRH admissions.
The two rank proofs and this wave enter one Codex audit.
[Proof report](fills/09-gadget-inversion/REPORT.md)

Gate 13 **passes** the two rank fills, seven gadget and recovery fills,
and the approved reader with zero blockers, majors, and minors. The auditor
replayed the 144-module closure and both probes. Intake verified the 247
sections at exchange `4cd97c861b80fb7d3ea7f40a772657c7aad367eb`.
[Findings](../../audits/lwe-sis-gadget-inversion-proofs-findings.md) ·
[Disposition](../../audits/lwe-sis-gadget-inversion-proofs-resolutions.md)

The counted-loop registration proposal pairs the existing FP contract with
the H14 clean-install and head-envelope contracts. The Lean specialization
passes using the existing owners. The maintainer approved the exact
one-row diff, applied at `2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11`. Gate 14 passed the host
entry with zero blockers, majors, and minors. The reviewer replayed the
45-module closure and both specializations. The seven efficiency fills
and two SIS CRH fills are the next proof wave.
[Counted-loop disposition](../../audits/lwe-sis-counted-loop-registration-resolutions.md)

## Counted-loop consumers and SIS collision resistance

The final seven efficiency and two asymptotic SIS proofs are filled at
`8b3187bdaf0c634c086313a727a7210dca14bfeb`. The 144-module replay passes with zero owned admissions and
17 inherited admission warnings. All 220 elaborated types match Gate 13.
The axiom inventory closes the nine admissions and records four compiler
auxiliaries. The nine proof bodies are ready for independent Gate 15 review.
[Proof report](fills/10-counted-loop-consumers/REPORT.md)

Merge clearance requires a passing Gate 15 review, scoped source matching,
and exact-target landing checks. The user approves all merges.
