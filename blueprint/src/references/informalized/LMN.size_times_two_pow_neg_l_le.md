<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN.lean :: size_times_two_pow_neg_l_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `s · 2^(−l) ≤ ε/2` when `l = log₂(2s/ε)`

**Claim.** For `s : ℕ` with `0 < s` and `ε : ℝ` with `0 < ε`,

`(s : ℝ) * (2 : ℝ)⁻¹ ^ Real.logb 2 (2 * s / ε) ≤ ε / 2`

(`Real.rpow`, since the exponent is a real logarithm). In fact equality holds —
the statement is phrased as `≤` because that is the form the LMN error budget
needs.

**Proof.** Unwind the exponential/logarithm pair, then simplify.

1. `Real.inv_rpow` (with `0 ≤ 2`) rewrites `2⁻¹ ^ a` as `(2 ^ a)⁻¹`.
2. `Real.rpow_logb` (base `≠ 0, 1`; argument `2 * s / ε` positive by
   `positivity`) collapses `2 ^ logb 2 (2 * s / ε)` to `2 * s / ε`, so the left
   side is `s * (2 * s / ε)⁻¹`.
3. With `0 < (s : ℝ)` (`Nat.cast_pos.mpr hs`), `field_simp` gives
   `(2 * s / ε)⁻¹ = ε / (2 * s)` and then `s * (ε / (2 * s)) = ε / 2`; rewriting
   with both closes the goal by reflexivity — the `s` cancels exactly.

**Used in.** `LMN/LMNConcentration.lean`, in the `calc` chain that splits the
concentration error into two halves of `ε`; this half absorbs the size factor `s`
coming from the union bound over gates.
