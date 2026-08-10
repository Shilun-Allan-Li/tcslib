<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: composedDelta_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The composed restriction parameter is at most one

**Claim.** For `w : ℕ`, `l : ℝ`, `d : ℕ` with `1 ≤ w` and `1 ≤ l` (and an
unused hypothesis `2 ≤ d`), `composedDelta w l d ≤ 1`, i.e.
`(1 / (40 * w)) * (1 / (40 * l)) ^ (d - 2) ≤ 1`.

**Proof.** A single `mul_le_one₀` application with three side goals:

1. `1 / (40 * w) ≤ 1` — `rw [div_le_iff₀]` then `norm_cast` and `linarith`
   from `1 ≤ w`.
2. `0 ≤ (1 / (40 * l)) ^ (d - 2)` — `positivity`.
3. `(1 / (40 * l)) ^ (d - 2) ≤ 1` — `pow_le_one₀`, whose base bound
   `1 / (40 * l) ≤ 1` is again `div_le_iff₀` plus `linarith` from `1 ≤ l`. ∎

Together with `composedDelta_pos` this is the pair of facts that lets
`composedDelta w l d` be used as a Bernoulli parameter. The `2 ≤ d` argument is
named `_hd` and is genuinely unused: natural subtraction makes the exponent `0`
for small `d`, and the bound holds anyway.

**Used in.** `circuit_reduction_ind_base`, `circuit_reduction_ind_step`, and
`LMN/LMNConcentration.lean`.
