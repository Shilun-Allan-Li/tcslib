<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: mem_freeVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Membership in the free set means the coordinate is unfixed

**Claim.** For a restriction `ρ : Restriction n` and a coordinate `i : Fin n`,

`i ∈ ρ.freeVars ↔ ρ i = none`.

**Proof.** Immediate from `simp [Restriction.freeVars, Option.isNone_iff_eq_none]`.
Unfolding `Restriction.freeVars ρ = Finset.univ.filter (fun i => (ρ i).isNone)`
turns membership into `(ρ i).isNone = true`, and
`Option.isNone_iff_eq_none` rewrites that to `ρ i = none`.

**Remark.** A deliberately granular interface lemma: `freeVars` is defined as a
`Finset.filter`, so every later argument that needs to move between "`i` is
free" and "`ρ i = none`" would otherwise re-unfold the filter. Both directions
are used — `.mp` to extract `ρ i = none`, `.mpr` (usually contrapositively) to
show a coordinate is fixed.

**Used in.** `chiS_extend`, `indicator_signProd_eq_prod`, and repeatedly in
`TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean`.
