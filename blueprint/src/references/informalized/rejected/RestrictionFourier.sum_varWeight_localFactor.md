<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: sum_varWeight_localFactor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Averaging one local factor

**Claim.** For `p : ℝ`, finsets `U S : Finset (Fin n)` and a coordinate `i`,

`∑ v : Option Bool, varWeight p v * localFactor U S i v`
` = if i ∈ S then p else if i ∈ U then 0 else 1`.

**Proof.** One line:
`by_cases hiS : i ∈ S <;> by_cases hiU : i ∈ U <;> simp [localFactor, varWeight, boolToSign, hiS, hiU] <;> ring`.
The four cases are the whole content, each a three-term sum over `Option Bool`:

- `i ∈ S`: only `v = none` survives the local factor, contributing
  `varWeight p none = p`.
- `i ∉ S`, `i ∈ U`: `none` is killed by the local factor and the two fixed values
  contribute `+1` and `−1` at equal weight `(1 - p)/2`, so the sign averages to `0`.
- `i ∉ S`, `i ∉ U`: the local factor is `1`, leaving the total coordinate mass
  `p + 2·((1 - p)/2) = 1`.

**Used in.** `expectation_fourierCoeff_restrictBF` (Proposition 4.17, first
identity): the `p` branch produces the factor `p ^ |S|`, and the `0` branch is
what forces `U = S` there.
