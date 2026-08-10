<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: indicator_signProd_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Indicator times sign is a product of local factors

**Claim.** Let `S ⊆ U` be finsets of `Fin n` and let `ρ` be a restriction, with
`J = ρ.freeVars`. Then

`(if U ∩ J = S then signProd ρ (U \ J) else 0) = ∏ i : Fin n, localFactor U S i (ρ i)`.

The indicator of the event `U ∩ J = S` multiplied by the sign `ρ` contributes on
`U \ J` is exactly the coordinatewise product of `localFactor`s. (For `S ⊄ U` the
indicator is identically `0` and the hypothesis is not needed elsewhere.)

**Proof.** `by_cases hcond : U ∩ J = S`.

- **Event holds.** Prove the pointwise identity `hpt`:
  `localFactor U S i (ρ i) = if i ∈ U \ S then boolToSign ((ρ i).getD false) else 1`,
  by cases on `i`:
  - `i ∈ S`: then `i ∈ U ∩ J` by `hcond`, so `ρ i = none` (`mem_freeVars.mp`) and
    `i ∉ U \ S`; both sides are `1` (`simp [localFactor]`).
  - `i ∉ S`, `i ∈ U`: `ρ i ≠ none`, since otherwise `i ∈ U ∩ J = S`
    (`mem_freeVars.mpr`); and `i ∈ U \ S`. `cases hv : ρ i` kills `none` and
    gives the sign in the `some b` case.
  - `i ∉ U`: `i ∉ U \ S`, both sides `1`.
  Then `Finset.prod_congr`, `Finset.prod_ite_mem` and `Finset.univ_inter`
  collapse the product to one over `U \ S`, and `hset : U \ J = U \ S`
  (from `← hcond` by `ext`/`tauto`) matches it with `signProd ρ (U \ J)`.
- **Event fails.** `by_contra`/`push_neg`: if every local factor were nonzero
  then `U ∩ J = S` follows by `ext` — the forward inclusion from the `i ∈ S`
  branch of `localFactor`, the reverse from `S ⊆ U` plus the fixed-coordinate
  branch — contradicting `hcond`. So some factor vanishes and
  `Finset.prod_eq_zero` gives `0`.

**Used in.** Both Proposition 4.17 identities: it is the step that puts the
summand into the coordinatewise form `sum_bernoulli_prod` consumes.
