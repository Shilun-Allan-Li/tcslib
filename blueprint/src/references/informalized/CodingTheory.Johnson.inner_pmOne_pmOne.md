<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: inner_pmOne_pmOne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Inner product of two sign vectors is `n - 2·hdist`

**Claim.** For all `x y : BitVec n`, the real inner product of their `±1`
encodings satisfies `⟪pmOne x, pmOne y⟫_[ℝ] = n - 2 * hdist x y`, where
`pmOne x i = if x i then -1 else 1` and `hdist x y` is the number of
coordinates on which `x` and `y` differ.

**Proof.**

1. Coordinatewise, `coord_mul_pmOne x y i` gives
   `pmOne x i * pmOne y i = if x i = y i then 1 else -1` (four-case `by_cases`
   on `x i`, `y i` plus `simp [pmOne]`).
2. `hdist x y` is rewritten as an indicator sum
   `∑ i, if x i ≠ y i then 1 else 0`, via `Finset.sum_ite` together with
   `Finset.filter_congr` on the defining filter (`aesop` for the predicate
   equivalence).
3. `simp_all [RCLike.wInner]` unfolds the inner product into
   `∑ i, pmOne x i * pmOne y i`, and a second `simp_all [Finset.sum_ite]`
   splits that sum into the agreeing coordinates (contributing `+1`) and the
   disagreeing ones (contributing `-1`).
4. `Finset.filter_not` and `Finset.card_sdiff` turn the count of agreeing
   coordinates into `n - hdist x y`, so the sum is
   `(n - hdist x y) - hdist x y`.
5. `Nat.cast_sub` (with `Finset.card_le_univ` supplying the subtraction
   side condition) moves the truncated ℕ-subtraction into ℝ, and `ring`
   finishes.

**Used in.** `inner_shifted_le_expr`, which combines it with
`inner_pmOne_ones` and `inner_ones_ones` to evaluate `⟪shifted α x, shifted α y⟫`.
