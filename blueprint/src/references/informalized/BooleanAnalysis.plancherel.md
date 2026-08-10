<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: plancherel -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.72) -->

# Plancherel's identity for two Boolean functions

**Claim.** For all `f g : BooleanFunc n`, the `L²` inner product under the
uniform measure equals the sum of products of Fourier coefficients:
`innerProduct f g = ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S`.

**Proof.** The whole argument is one `have expand` followed by orthonormality.

1. Unfold `innerProduct`, `expect`, `uniformWeight` so the goal is
   `2⁻ⁿ · ∑_x f x * g x`, and replace each pointwise product by the product of
   the two Walsh expansions (`walsh_expansion f x`, `walsh_expansion g x`).
2. Push the scalar `2⁻ⁿ` through the `x`-sum and expand the product of the two
   `S`- and `T`-sums into a triple sum over `x, S, T`
   (`Finset.mul_sum`, `Finset.sum_mul`, under `Finset.sum_congr rfl`).
3. Move the `x`-sum innermost with two applications of `Finset.sum_comm`, then
   factor `fourierCoeff f S * fourierCoeff g T` out of it (`ring` pointwise,
   then `← Finset.mul_sum` twice). This leaves
   `2⁻ⁿ · ∑_x chiS S x * chiS T x`, i.e. `innerProduct (chiS S) (chiS T)`, so
   `expand : innerProduct f g = ∑ S ∑ T, f̂ S * ĝ T * ⟪χ_S, χ_T⟫`.
4. `rw [expand]`, then orthonormality `fourier_coeff_chi` turns each
   `⟪χ_S, χ_T⟫` into `if S = T then 1 else 0`; `mul_ite, mul_one, mul_zero`
   and `Finset.sum_ite_eq, Finset.mem_univ, if_true` collapse the inner
   `T`-sum to its diagonal term, giving the claimed sum. ∎

**Remark.** This is the substantive result of the inner-product group: it is the
bilinear (two-function) generalisation of `parseval`, whose proof it mirrors
step for step with `g` in place of the second `f`. It is used to prove
`noiseOp_self_adjoint` (Plancherel forwards, then backwards, around a
`ρ ^ |S|` reshuffle of the coefficients).
