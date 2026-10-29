<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: sum_varWeight_localFactor_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Averaging a product of two local factors

**Claim.** For `p : ℝ`, finsets `U V S : Finset (Fin n)` and a coordinate `i`,

`∑ v : Option Bool, varWeight p v * (localFactor U S i v * localFactor V S i v)`
` = if i ∈ S then p else if i ∈ U ∧ i ∈ V then (1 - p) else if i ∈ U ∨ i ∈ V then 0 else 1`.

**Proof.** One line: `by_cases` on `i ∈ S`, `i ∈ U`, `i ∈ V` and then
`simp [localFactor, varWeight, boolToSign, ...] <;> ring`. The eight cases:

- `i ∈ S`: both factors keep only `v = none`, giving `varWeight p none = p`.
- `i ∉ S`, `i ∈ U ∩ V`: both factors are the same sign, whose square is `1`, so
  the two fixed values contribute `2·((1 - p)/2) = 1 - p` and `none` contributes `0`.
- `i ∉ S`, `i` in exactly one of `U`, `V`: one unsquared sign remains and
  averages to `0`.
- `i` in none of `S`, `U`, `V`: both factors are `1`, total mass `1`.

**Used in.** `expectation_fourierCoeff_sq_restrictBF` (Proposition 4.17, second
identity). The second branch is the source of the `(1 - p) ^ |U \ S|` factor, and
the third is what forces `U = V` in the double sum over Fourier coefficients.
