<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: binaryEntropy_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binary entropy vanishes at zero

**Claim.** `binaryEntropy 0 = 0`, where
`binaryEntropy x = -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)`.

**Proof.** Immediate from `unfold binaryEntropy; norm_num`: the first summand is
`-0 * Real.logb 2 0 = 0` regardless of the logarithm's value, and the second is
`-(1 - 0) * Real.logb 2 (1 - 0) = -Real.logb 2 1 = 0` by `Real.logb_one`.

**Remark.** No `0 * log 0` side condition is needed: Mathlib's `Real.logb 2 0`
is defined to be `0`, so the convention `0 · log₂ 0 = 0` recorded in the
`binaryEntropy` docstring holds definitionally rather than by hypothesis. This
and `binaryEntropy_half` are the two endpoint evaluations of `H` used when
specializing the MRRW bound (`mrrw_bound`) at `δ = 0` and `δ = 1/2`.
