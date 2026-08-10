<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: signProd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Product of the signs a restriction fixes on a set

**Definition.** For a restriction `ρ : Restriction n = Fin n → Option Bool` and a
set `T : Finset (Fin n)`,

`signProd ρ T = ∏ i ∈ T, boolToSign ((ρ i).getD false) : ℝ`,

the product over `i ∈ T` of the ±1-encoding of the bit that `ρ` fixes at `i`
(`boolToSign false = 1`, `boolToSign true = -1`).

**Remark.** On a free coordinate (`ρ i = none`) the `getD false` default supplies
the junk value `1`. This is harmless because `signProd` is always used in the
form `signProd ρ (U \ ρ.freeVars)`, where every coordinate is genuinely fixed, or
underneath an indicator that forces this.

**Used in.** `chiS_extend`, `fourierCoeff_restrictBF`,
`indicator_signProd_eq_prod`, `signProd_sq`, and both identities of O'Donnell
Proposition 4.17 in this file.
