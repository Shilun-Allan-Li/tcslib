<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: floor_np_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The floor of n·p is positive for large n

**Claim.** Let `0 < p` and `0 < 1 - p`, let `N₂ = ⌈2 / (p(1-p))⌉ + 1`, and let
`n : ℕ` with `N₂ ≤ n`. Then `0 < ⌊(n:ℝ) * p⌋₊`. A `private` threshold helper: past
`N₂` the radius `⌊np⌋` is at least `1`.

**Proof.** By contradiction on the floor being zero.

1. `Nat.pos_of_ne_zero`, then `intro heq` with `heq : ⌊(n:ℝ)·p⌋₊ = 0`;
   `Nat.floor_eq_zero.mp` gives `(n:ℝ)·p < 1`.
2. `0 < p(1-p)` (`mul_pos`), and `N₂ ≤ n` casts to `(N₂:ℝ) ≤ n`
   (`exact_mod_cast`).
3. Unfolding `N₂` and using `Nat.le_ceil` gives `2/(p(1-p)) + 1 ≤ (N₂:ℝ)`, hence
   `2/(p(1-p)) + 1 ≤ n` (`le_trans`).
4. Multiplying that by `p(1-p) > 0` (`mul_le_mul_of_nonneg_right`) and clearing the
   division with `field_simp` yields `2 + p(1-p) ≤ n · p(1-p)`.
5. But `p < 1`, so `n·p(1-p) ≤ n·p < 1`, contradicting `2 + p(1-p) > 1`. The final
   `nlinarith` combines exactly these products. ∎

**Used in.** `binomial_coef_asymptotic_lower_bound'`, where `a = ⌊np⌋` must be
positive before its factorial and the `a^a` denominators can be handled.
