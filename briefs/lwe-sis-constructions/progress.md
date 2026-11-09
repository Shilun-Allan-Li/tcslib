# Campaign pulse

The combined statement and independent 31-proof audits each pass **0 blockers,
0 majors, 1 documentation minor and 4 notes** on draft
[#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250). Both documentation
minors are corrected separately and checked. Eleven scoped gates now pass.

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
bound and leave **58 owned admissions**. The combined audit reviews the two
reader equations and the six proofs as separate scopes. See
[the statistical hybrid report](fills/06-regev-statistical/REPORT.md).

| Part | Current progress | Remaining work |
|---|---|---|
| DLWE/SIS foundations and sampling | Foundations, exact dyadic laws, bit-noise probability/support/symmetry/mean and common-secret sampling/test laws proved and audited | Efficient uniform family samplers and schedules, source policy |
| Direct Regev symmetric encryption | Algorithms, bounded-error correctness and concrete two-DLWE bound proved and audited | Efficient implementations, uniform message bounds and final existing-game bridge |
| SIS collision-resistant hashing | Core hash/reduction/profile audited. Universality and strong extraction checked on the new stack | Raw collision and evaluator proofs, counted-loop disposition, final CRH interface under independent SIS hardness |
| Regev CPA PKE | Every-coin correctness and hybrid support audited. Statistical hybrid and final finite fixed-bit bound checked | Combined proof audit, efficiency and CPA interface |
| PRGs | All eleven structured/MSB/flat generator obligations proved and audited with complete seed budgets | Efficient family schedules and standard exact-seed asymptotic PRG integration |
| CCA2 PKE | Secret-matrix lossy/all-but-one mathematics and DLWE column-hybrid statements pass | Supporting fills, pending reader disposition, all-but-one inverse, strong one-time signatures and final CCA2 proof |

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

**Not yet clear to merge.** The new reader and consumer scopes await audit.
#250 retains 58 admissions, other shared-owner holds, scoped source review
and landing checks. The user approves all merges.
