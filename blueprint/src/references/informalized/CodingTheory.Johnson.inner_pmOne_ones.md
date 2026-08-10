<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: inner_pmOne_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Inner product of a sign vector with the all-ones vector is `n - 2·wt`

**Claim.** For every `x : BitVec n`,
`⟪pmOne x, ones⟫_[ℝ] = n - 2 * wt x`, where `ones` is the constant-`1`
vector in `Euc n` and `wt x` counts the coordinates where `x` is `true`.

**Proof.**

1. `simp [RCLike.wInner]` expands the inner product to
   `∑ i, pmOne x i * ones i`.
2. `Finset.sum_congr` plus `unfold pmOne ones; aesop` rewrites each summand
   as `if x i then -1 else 1`.
3. `simp_all [Finset.sum_ite]` splits the sum over the `true`-set and the
   `false`-set of `x`, giving `#{i | x i = false} - #{i | x i = true}`.
4. The `false`-filter is rewritten as `univ \ {i | x i = true}`
   (`ext; aesop`), so `Finset.card_sdiff` turns its cardinality into
   `n - wt x`.
5. `Nat.cast_sub` (side condition from `Finset.card_le_univ`) pushes the
   subtraction into ℝ and `ring` closes the goal.

**Used in.** `inner_shifted_le_expr` — this is the term that converts the
`α • ones` shift into the weight constraint `wt x ≤ w`.
