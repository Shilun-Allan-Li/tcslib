<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: shifted_ne_zero_of_alpha_lt_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The shifted sign vector is nonzero when the shift is below one

**Claim.** For `n > 0`, a real shift `α` with `0 ≤ α < 1`, and any bit vector
`x : BitVec n`, the vector `shifted α x = pmOne x - α • ones` is not the zero
vector of `Euc n`.

**Proof.** Suppose `shifted α x = 0`.

1. Evaluate at the coordinate `i = ⟨0, hn⟩` (which exists because `0 < n`):
   `congrArg (fun v => v i)` plus `simpa` gives `shifted α x i = 0`.
2. Case on the bit `x i` (`by_cases hx : x i`):
   - if `x i = true`, then `simp [shifted, pmOne, ones, hx]` gives
     `shifted α x i = -1 - α`, and `-1 - α = 0` contradicts `0 ≤ α`
     (`linarith`);
   - if `x i = false`, then the same `simp` gives `shifted α x i = 1 - α`, and
     `1 - α = 0` contradicts `α < 1` (`linarith`).

**Remark.** Only one coordinate is inspected — every coordinate of `pmOne x` is
`±1`, so no coordinate of the shift can be cancelled unless `α` reaches `1`.

**Used in.** `binary_johnson_card_bound`, where it discharges the `hnonzero`
hypothesis of `binary_johnson_card_bound_parametric` for `α = alpha n d` (using
`alpha_nonneg` and `alpha_lt_one_of_hd1`); nonzero-ness is what makes
`normalize` produce genuine unit vectors for the Rankin bound.
