<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: signProd_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The squared sign product is 1

**Claim.** For every restriction `ρ : Restriction n` and every
`T : Finset (Fin n)`, `signProd ρ T ^ 2 = 1`.

**Proof.** Three rewrites.

1. `rw [signProd, ← Finset.prod_pow]` unfolds the definition and moves the square
   inside the product, factor by factor.
2. `Finset.prod_congr rfl` with `boolToSign_sq ((ρ i).getD false)` turns each
   factor into `1`.
3. `Finset.prod_const_one` closes the goal.

**Remark.** No hypothesis on `T`: even the junk `getD false` values that
`signProd` produces on free coordinates are `±1`, so they square to `1` as well.

**Used in.** `bernoulliRestrProb_inter_freeVars`, where the squared restricted
Fourier coefficient of a character `χ_U` collapses to the indicator of
`U ∩ ρ.freeVars = S`.
