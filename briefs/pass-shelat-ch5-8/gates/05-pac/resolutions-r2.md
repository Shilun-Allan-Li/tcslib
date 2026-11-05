# Gate 05 (PAC layer, #194): round 2 resolutions

- **Round 2:** findings `findings/gate05-pac-r2-findings.md` on #194 at `6b781240`: **1 major (R2-1),
  2 minors (R2-2, R2-3)**; F1 (round 1's major) fixed; F5, F6, F11 and F14 not resolved; the others
  fixed or recorded.
- **Repair:** one commit on #194's branch, `f0385dac9ff477ef2debff7336d454b1a28b8818`, docstrings and
  module docstrings only (the four modules with comments stripped are byte-identical to `6b781240`).
  Maintainer re-check: the four modules pass in import order with no diagnostics; lint 0. Records:
  the S3d design note's bridge bullet and its `PACLearns` argument order (this commit's records
  companion).

| Item | Severity | Resolution |
|---|---|---|
| R2-1 | major | **Fixed.** `WeakLearnsUnder` ("the weak-learning condition under `D`"), `WeakLearns` and `not_weakLearnsUnder_of_predictAdv_le` no longer attribute an arbitrary-confidence requirement to [KV94, §4.1] nor present fixing the confidence as a relaxation for the same learner. They state [KV94, §4.1, p. 74]'s weak learner (success probability `1/q`, edge `1/p`), that it satisfies the predicate at `δ = 1 − 1/q`, that a smaller `δ` is a stronger requirement for the same learner, and that reaching it needs confidence amplification [KV94, §4.2, pp. 76–77], a different learner. `Prediction.lean`'s module docstring gains a "Use in layer 2" paragraph recording that obligation; the `Defs.lean` "Unrestricted parameters" bullet, the main-definition and main-result lines and the `PAC.lean` contents line are aligned; the [KV94] references list §4.1 (p. 74) and §4.2 (pp. 76–77). |
| R2-2 | minor | **Fixed.** `Prediction.lean`'s module docstring states `γ + δ < γ' ≤ ½` and the expectation split (accuracy event, error ≤ `ε`; complement, probability ≤ `δ`, error ≤ 1). The S3d design note's "Markov on the error" sentence is replaced by the same argument and the amplification obligation. |
| R2-3 | minor | **Fixed.** [SSBD14] locations adopted as verified by the auditor: §2.3.1 (product sampling) and §3.1, Definition 3.1 (i.i.d. examples), in `Samples.lean`'s references and `iid`'s docstring; the unverified notation claim `S ~ D^m` dropped. |
| F5, F6 | (round 1) | **Fixed by R2-1** (the [KV94, §4.1] comparison corrected); **amends** `resolutions-r1.md`, which marked them fixed in round 1. |
| F11 | (round 1) | **Fixed in round 2** with R2-2 (the design note's sentence); amends round 1's "fixed". |
| F14 | (round 1) | **Fixed in round 2:** [SSBD14, §3.1] retained and verified by the round 2 auditor (Def 3.1 uses i.i.d. samples); [SSBD14, §2.3.1] (product sampling) added. |
| M10 (review, round 1) | minor | **Fixed:** the design note's `PACLearns` argument order is the code's, `C m L ε δ`. |
