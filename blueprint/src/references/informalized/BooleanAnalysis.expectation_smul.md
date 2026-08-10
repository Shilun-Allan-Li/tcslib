<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: expectation_smul -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.90) -->

# The expectation operator commutes with scalars

**Claim.** For `i : Fin n`, `c : ℝ` and `f : BooleanFunc n`,
`expectationOperator i (c • f) = c • expectationOperator i f`, where
`expectationOperator i f x = (f (Function.update x i false) + f (Function.update x i true)) / 2`.

**Proof.**

1. `ext x` reduces to a pointwise identity in ℝ.
2. Unfold the operator and the scalar action
   (`simp only [expectationOperator, Pi.smul_apply, smul_eq_mul]`), so both
   sides are built from `c` and the two values of `f` at the `Function.update`
   points.
3. `ring` discharges the identity `(c * a + c * b) / 2 = c * ((a + b) / 2)`. ∎

**Used in.** Supplies `map_smul'` for `expectationLm`; with `expectation_add`
it makes `expectationOperator i` a linear endomorphism of `BooleanFunc n`.
