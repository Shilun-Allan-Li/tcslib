<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: innerProduct_comm -->
<!-- origin: boolean-ch01-fourier-blr run cdca27e1b5fd verdict not_in_text (0.86) -->

# Symmetry of the Boolean inner product

**Claim.** For all `f g : BooleanFunc n`, `innerProduct f g = innerProduct g f`.

**Proof.**

1. Unfold `innerProduct` and `expect`: both sides are
   `uniformWeight n * ∑ x, f x * g x` resp. `uniformWeight n * ∑ x, g x * f x`,
   with the same scalar weight.
2. The summands agree pointwise by commutativity of real multiplication
   (`mul_comm`), so the sums agree termwise.

Both steps are discharged by the single tactic
`simp [innerProduct, expect, mul_comm]`. ∎

**Remark.** One of four deliberately granular bilinearity building blocks
(`innerProduct_add_left`, `innerProduct_comm`, `innerProduct_self_nonneg`,
`innerProduct_self_pm_one`) that record the inner-product axioms explicitly
rather than routing through a Mathlib `InnerProductSpace` instance.
