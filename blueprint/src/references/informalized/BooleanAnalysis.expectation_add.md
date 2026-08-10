<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: expectation_add -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.86) -->

# The expectation operator is additive

**Claim.** For `i : Fin n` and `f g : BooleanFunc n`,
`expectationOperator i (f + g) = expectationOperator i f + expectationOperator i g`,
where `expectationOperator i f x = (f (Function.update x i false) + f (Function.update x i true)) / 2`.

**Proof.**

1. `ext x` reduces the equality of functions to a pointwise identity in ℝ.
2. Unfold the operator and pointwise addition
   (`simp only [expectationOperator, Pi.add_apply]`), turning both sides into
   sums of the four values of `f` and `g` at the two `Function.update` points,
   divided by `2`.
3. `ring` closes the resulting real-arithmetic identity. ∎

**Used in.** Together with `expectation_smul`, this is the `map_add'` field of
`expectationLm`, the linear-map packaging of `expectationOperator`.
