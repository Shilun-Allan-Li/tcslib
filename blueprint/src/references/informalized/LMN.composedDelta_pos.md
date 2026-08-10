<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: composedDelta_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The composed restriction parameter is positive

**Claim.** For `w : ℕ`, `l : ℝ` and `d : ℕ`, if `0 < w` and `0 < l` then
`0 < composedDelta w l d`, where
`composedDelta w l d = (1 / (40 * w)) * (1 / (40 * l)) ^ (d - 2)`.

**Proof.** Immediate from `unfold composedDelta; positivity`: both factors are
positive because `40 * w > 0` and `40 * l > 0`, and a positive base raised to a
natural power stays positive.

One remark: `d` plays no role. The exponent `d - 2` is truncated natural
subtraction, so for `d < 2` the second factor is just `1` and the statement
still holds — no `2 ≤ d` hypothesis is needed here.

**Used in.** The side conditions of `circuit_reduction_ind_base`,
`circuit_reduction_ind_step` and, outside this file,
`LMN/LMNConcentration.lean`, wherever `composedDelta` has to be shown to be a
legal Bernoulli parameter.
