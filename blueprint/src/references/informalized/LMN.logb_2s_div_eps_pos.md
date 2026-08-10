<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN.lean :: logb_2s_div_eps_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The LMN parameter `l = log₂(2s/ε)` is at least 1

**Claim.** For `s : ℕ` with `0 < s` and `ε : ℝ` with `0 < ε ≤ 1`,

`1 ≤ Real.logb 2 (2 * s / ε)`.

This is the sanity check that the LMN degree/depth parameter
`l = log₂(2s/ε)` is a usable (positive) bound: `2s/ε ≥ 2` under these
hypotheses.

**Proof.** Monotonicity of `logb 2` against the value `logb 2 2 = 1`.

1. Rewrite the goal's `1` as `Real.logb 2 2` (`Real.logb_self_eq_one`, with
   `h2 : (1:ℝ) < 2` by `norm_num`).
2. Apply `Real.logb_le_logb` in the `.mpr` direction: it suffices that
   `2 ≤ 2 * s / ε`, the positivity side conditions being `norm_num` /
   `positivity`.
3. `rw [le_div_iff₀ hε_pos]` turns that into `2 * ε ≤ 2 * s`, which follows from
   `ε ≤ 1` and `1 ≤ (s : ℝ)` (`Nat.one_le_cast.mpr hs`) by `nlinarith`.

**Used in.** `LMN/LMNConcentration.lean`, where `l = logb 2 (2s/ε)` is the
degree cutoff for the Fourier-concentration statement.
