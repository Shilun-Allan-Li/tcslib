<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: q_pow_qary_entropy_simp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Closed form for q raised to the q-ary entropy

**Claim.** For `q : ℕ` with `2 ≤ q` and `p : ℝ` with `0 < p < 1`,

```
q ^ (qaryEntropy q p) = (q - 1)^p · p^(-p) · (1 - p)^(-(1-p)),
```

all powers being `Real.rpow`. This is `H_q(p)`'s exponent written as an elementary
product.

**Proof.** Split the `rpow` of a sum into a product, then cancel each `rpow ∘ logb`.

1. `dsimp only [qaryEntropy]` unfolds the entropy, and
   `qary_entropy_logb_expand q p` rewrites the exponent into the form
   `logb q (q-1)·p + logb q p·(-p) + logb q (1-p)·(-(1-p))`.
2. Side facts: `0 < (q:ℝ)`, `(q:ℝ) ≠ 1`, `0 < (q:ℝ) - 1`
   (`natCast_pos_of_two_le`, `natCast_ne_one_of_two_le`,
   `natCast_sub_one_pos_of_two_le`) and `0 < 1 - p` (`one_sub_pos_of_lt_one`).
3. `Real.rpow_add` (twice) turns the three-term exponent into a product of three
   powers of `q`.
4. `Real.rpow_mul` (three times) rewrites each `q ^ (logb q x · e)` as
   `(q ^ logb q x) ^ e`.
5. `Real.rpow_logb` (three times, with the positivity facts from step 2) collapses
   `q ^ logb q x` to `x` for `x = q-1`, `p`, `1-p`.
6. `simp only [neg_sub]` normalises `-(1-p)` to match the goal. ∎

**Used in.** The Gilbert–Varshamov / ball-counting arguments, where the entropy
exponent must be compared against explicit products of `(q-1)^p`, `p^(-p)` and
`(1-p)^(-(1-p))`; `q_pow_qary_entropy_simp'` is the `Monoid.npow`-flavoured variant.
