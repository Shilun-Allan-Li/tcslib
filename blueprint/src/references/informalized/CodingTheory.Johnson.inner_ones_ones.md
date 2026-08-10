<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: inner_ones_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The all-ones vector has squared norm `n`

**Claim.** `⟪ones (n := n), ones (n := n)⟫_[ℝ] = n`, where
`ones : Euc n` is the constant-`1` vector.

**Proof.** Immediate from `simp [RCLike.wInner, ones]`: unfolding the inner
product gives `∑ i : Fin n, 1 * 1`, which `simp` evaluates to `n` via
`Finset.card_univ`.

**Used in.** `inner_shifted_le_expr`, as the `α^2 * n` term of the expansion
produced by `inner_shifted_expand`.
