<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: alpha_lt_one_of_hd1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The shift parameter is strictly below one

**Claim.** If `0 < n`, `1 ≤ d` and `2 * d ≤ n`, then `alpha n d < 1`, where
`alpha n d = Real.sqrt ((n - 2*d)/n)`.

**Proof.**

1. `(n - 2*d : ℝ) / n < 1`: since `1 ≤ d` the numerator is strictly smaller
   than `n` (`norm_num [hd1]`), so `div_lt_one` (with `positivity` for
   `0 < n`) converts the strict fraction bound.
2. `Real.sqrt ((n - 2*d)/n) < Real.sqrt 1` by `Real.sqrt_lt_sqrt`, whose two
   side goals are radicand nonnegativity (`div_nonneg` with
   `sub_nonneg_of_le` from `hd`) and step 1.
3. `convert … using 1` then `simp [Real.sqrt_one]` identifies `Real.sqrt 1`
   with `1` and unfolds `alpha`.

**Used in.** `binary_johnson_card_bound`, where `α < 1` is exactly what
`shifted_ne_zero_of_alpha_lt_one` needs: with `α < 1` no coordinate of
`pmOne x - α • ones` can vanish, so every shifted codeword is nonzero and can
be normalized.
