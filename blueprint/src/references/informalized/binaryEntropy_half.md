<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: binaryEntropy_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Binary entropy equals one at one half

**Claim.** `binaryEntropy (1 / 2) = 1`, for
`binaryEntropy x = -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)`.

**Proof.** Two steps.

1. `unfold binaryEntropy; norm_num` reduces the goal to an identity in
   `Real.logb 2 (1 / 2)`, both summands having collapsed to the same
   `1/2`-weighted term since `1 - 1/2 = 1/2`.
2. `norm_num [Real.logb_div]` rewrites
   `Real.logb 2 (1 / 2) = Real.logb 2 1 - Real.logb 2 2 = -1`, so the value is
   `-(1/2)·(-1) - (1/2)·(-1) = 1`.

**Remark.** The `1` on the right is where the base-2 normalization is visible:
`binaryEntropy` is defined with `Real.logb 2` rather than `Real.log`, so it is
measured in bits and is not Mathlib's `Real.binEntropy` (which would give
`log 2` here). Together with `binaryEntropy_zero` this pins the two endpoints of
`H` on `[0, 1/2]`, the interval on which `mrrw_bound` is stated.
