<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN.lean :: logb_2_div_eps_le_l -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `log₂(2/ε) ≤ log₂(2s/ε)` for `s ≥ 1`

**Claim.** For `s : ℕ` with `0 < s` and `ε : ℝ` with `0 < ε`,

`Real.logb 2 (2 / ε) ≤ Real.logb 2 (2 * s / ε)`.

Enlarging the numerator from `2` to `2s` can only increase the logarithm. It lets
the two LMN parameters `log₂(2/ε)` (no size factor) and `l = log₂(2s/ε)` (with
the circuit size `s`) be compared.

**Proof.** One application of monotonicity.

1. `Real.logb_le_logb` (with `h2 : (1:ℝ) < 2` by `norm_num`, and both arguments
   positive by `positivity`), used in the `.mpr` direction, reduces the goal to
   `2 / ε ≤ 2 * s / ε`.
2. `rw [div_le_div_iff_of_pos_right hε_pos]` cancels the common positive
   denominator, leaving `2 ≤ 2 * s`, which `nlinarith` gets from
   `1 ≤ (s : ℝ)` (`Nat.one_le_cast.mpr hs`).

**Note.** A granular arithmetic helper; it is not currently referenced elsewhere
in the library.
