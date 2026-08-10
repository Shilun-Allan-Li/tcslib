<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: coeffs_granular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every coefficient is an integer multiple of `2^(-depth)`

**Claim.** For `T : DecisionTree n` and `S : Finset (Fin n)`, there is an integer
`m` with `T.coeffs S = (m : ℝ) / 2 ^ T.depth`.

**Proof.** Two lines.

1. `obtain ⟨m, hm⟩ := coeffs_mul_two_pow_int T T.depth le_rfl S` — the
   multiplicative form at the exponent `k = T.depth`, giving
   `T.coeffs S * 2 ^ T.depth = (m : ℝ)`.
2. The same `m` works: `eq_div_iff` converts the division form into that
   product, its nonvanishing side condition `(2 : ℝ) ^ T.depth ≠ 0` discharged
   by `positivity`, and `exact hm` finishes.

A thin division-form repackaging of `coeffs_mul_two_pow_int`; all the induction
lives there.

**Used in.** `fourierCoeff_granular` (O'Donnell Proposition 3.16, granularity),
and through it `sparsity_le`, where the bound `|m| ≥ 1` for nonzero `m` turns
granularity into the lower bound `2^(-depth)` on each nonzero coefficient.
