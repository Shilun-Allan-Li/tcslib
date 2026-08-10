<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: composeRestr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Composition of two restrictions

**Definition.** For `ρ₁ ρ₂ : Restriction n` (that is, `Fin n → Option Bool`),
`composeRestr ρ₁ ρ₂ : Restriction n` is the coordinatewise fallback

`composeRestr ρ₁ ρ₂ i = (ρ₁ i).orElse (fun _ => ρ₂ i)`,

so coordinate `i` keeps the value `ρ₁` fixes it to, and takes `ρ₂ i` only where
`ρ₁ i = none`. This models applying `ρ₁` first and then `ρ₂` to the variables
`ρ₁` left free.

**Remark.** `ρ₁` has strict priority, so the operation is not symmetric; `ρ₂`
is never consulted on coordinates already fixed. The all-free restriction
`fun _ => none` is a right identity (`composeRestr_id_right`).

**Used in.** `composeRestr_eq_iff`, `compose_fiber_weight_eq`,
`restriction_compose_eq`, `restriction_compose_le`, and downstream in
`RecursiveReduction.lean` (`restrictFn_composeRestr`: restricting by a
composition is restricting twice) and `Depth3Switching.lean`.
