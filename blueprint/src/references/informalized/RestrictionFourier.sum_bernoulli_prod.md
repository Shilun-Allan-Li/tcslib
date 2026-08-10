<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: sum_bernoulli_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli-weighted sums of coordinatewise products factor

**Claim.** For `p : ℝ` and `h : Fin n → Option Bool → ℝ`,

`∑ ρ : Restriction n, bernoulliRestrWeight p ρ * ∏ i, h i (ρ i)`
` = ∏ i : Fin n, ∑ v : Option Bool, varWeight p v * h i v`,

i.e. the Bernoulli(`p`) weight can be absorbed coordinate by coordinate, each
factor becoming the `varWeight`-weighted average of `h i` over the three
possible values `none`, `some false`, `some true`. No hypothesis on `p`.

**Proof.**

1. `hsplit`: for each `ρ`,
   `bernoulliRestrWeight p ρ * ∏ i, h i (ρ i) = ∏ i, varWeight p (ρ i) * h i (ρ i)`,
   by `bernoulliRestrWeight_eq_prod` (the global weight is the product of the
   per-coordinate `varWeight`s) followed by `← Finset.prod_mul_distrib`.
2. `Finset.sum_congr rfl` rewrites every summand by `hsplit`.
3. `exact sum_restriction_prod` applied to `fun i v => varWeight p v * h i v`.

**Used in.** Both identities of O'Donnell Proposition 4.17
(`expectation_fourierCoeff_restrictBF`,
`expectation_fourierCoeff_sq_restrictBF`) and in
`TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean`. It is the workhorse that
replaces the textbook's two-stage average (first over the fixed bits, then over
the free set) with a single coordinatewise computation.
