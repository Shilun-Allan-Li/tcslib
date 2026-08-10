<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: alpha -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `alpha n d`: the shift parameter

**Definition.** `alpha n d : ℝ` is `Real.sqrt (((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ))`
— the amount by which the all-ones vector is subtracted when a codeword's sign
vector `pmOne x` is turned into `shifted (alpha n d) x = pmOne x - alpha n d • ones`.

Its three properties, each proved separately in the file:

- `alpha_nonneg` : `0 ≤ alpha n d`, immediate from `Real.sqrt_nonneg`.
- `alpha_sq` : for `0 < n` and `2 * d ≤ n`, `(alpha n d)^2 = ((n : ℝ) - 2 * d) / n`
  (`Real.sq_sqrt` applied to the nonnegative argument).
- `alpha_lt_one_of_hd1` : for `0 < n`, `1 ≤ d`, `2 * d ≤ n`, `alpha n d < 1`
  (`(n - 2d)/n < 1` by `div_lt_one`, then `Real.sqrt_lt_sqrt` against
  `Real.sqrt 1`).

**Remark.** As with `J2`, no side condition is baked in: for `2 * d > n` or
`n = 0` the argument of the square root is negative or the division is by zero and
`Real.sqrt` returns `0`, so `alpha` is total and the hypotheses `0 < n`,
`1 ≤ d`, `2 * d ≤ n` travel with the lemmas.

**Used in.** `binary_johnson_card_bound` instantiates
`binary_johnson_card_bound_parametric` at `α := alpha n d`; `alpha_lt_one_of_hd1`
feeds `shifted_ne_zero_of_alpha_lt_one` and `johnson_arith` supplies the
arithmetic bound at that same value.
