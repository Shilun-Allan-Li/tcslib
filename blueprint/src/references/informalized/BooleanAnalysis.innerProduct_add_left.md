<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: innerProduct_add_left -->
<!-- origin: boolean-ch01-fourier-blr run cdca27e1b5fd verdict not_in_text (0.62) -->

# Additivity of the inner product in its first argument

**Claim.** For all `f g h : BooleanFunc n`,
`innerProduct (f + g) h = innerProduct f h + innerProduct g h`, where `+` is
the pointwise addition from the `Pi.addCommGroup` instance on `BooleanFunc n`.

**Proof.**

1. Unfold `innerProduct`, `expect`, `uniformWeight` and evaluate the pointwise
   sum with `Pi.add_apply`, then distribute each summand with `add_mul`:
   the left side becomes `2⁻ⁿ · ∑ x, (f x * h x + g x * h x)`.
2. Split the sum (`Finset.sum_add_distrib`) and distribute the scalar `2⁻ⁿ`
   over the resulting pair (`mul_add`), which is exactly the right side. ∎

**Remark.** One of four deliberately granular bilinearity building blocks;
together with `innerProduct_comm` it gives additivity in the second argument
for free.
