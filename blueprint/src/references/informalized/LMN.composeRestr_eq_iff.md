<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: composeRestr_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Composition of restrictions is decided coordinatewise

**Claim.** For `ρ₁ ρ₂ σ : Restriction n`, `composeRestr ρ₁ ρ₂ = σ` holds iff
`(ρ₁ i).orElse (fun _ => ρ₂ i) = σ i` for every coordinate `i`.

**Proof.** Pure function extensionality, no unfolding of `Option.orElse`
needed — the two sides of the definition of `composeRestr` are the same term.

- Forwards: `intro h i; exact congr_fun h i`.
- Backwards: `intro h; funext i; exact h i`.

**Remark.** A deliberately granular helper: it exists only to turn the
equality-of-functions side condition `composeRestr ρ₁ ρ₂ = σ` appearing inside
the indicator sums into a per-coordinate statement, which is the form the
product/fiber arguments need.

**Used in.** Nothing else in the library refers to it by name; the same
coordinatewise unfolding is instead done inline by
`simp [Finset.ext_iff, funext_iff, composeRestr]` inside
`compose_fiber_weight_eq`.
