<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: influence_chi -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.70) -->

# The influence of a character is the membership indicator

**Claim.** For `i : Fin n` and `S : Finset (Fin n)`,
`influence i (chiS S) = if i ∈ S then 1 else 0`: coordinate `i` has full
influence on the Walsh character `χ_S` when `i ∈ S` and none otherwise.

**Proof.** Unfold `influence`, `expect`, `uniformWeight` and split on `i ∈ S`.

- **Case `i ∈ S`.** By `chiS_flipBit`, `χ_S (flipBit x i) = -χ_S x`, so the
  summand is `(2 · χ_S x)^2 / 4 = χ_S x ^ 2`. With `chiS_sq_eq_one` this is `1`
  for every `x` (`field_simp`, `nlinarith`). The sum is therefore the constant
  `1` over the whole cube (`Finset.sum_const`, `Finset.card_univ`,
  `Fintype.card_pi`, `Fintype.card_bool`, `Finset.card_fin`), i.e. `2^n`, and
  the uniform weight cancels it: `(2:ℝ)⁻¹^n * 2^n = 1` via `← mul_pow` and
  `inv_mul_cancel₀`.
- **Case `i ∉ S`.** `chiS_flipBit` now gives `χ_S (flipBit x i) = χ_S x`, so
  each summand is `0` (`sub_self`, `zero_pow`, `zero_div`) and the whole
  expectation is `0` (`simp`). ∎

**Used in.** The base case for `influence_eq_sum_fourier`
(`Inf_i[f] = ∑_{S ∋ i} f̂(S)²`), which reads off the influence of a general `f`
from its Fourier expansion.
