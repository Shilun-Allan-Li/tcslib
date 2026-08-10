<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: restrictFn_composeRestr' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting by a composition is restricting twice

**Claim.** For `f : (Fin n → Bool) → Bool` and restrictions `ρ₁ ρ₂ :
Restriction n`,
`restrictFn f (composeRestr ρ₁ ρ₂) = restrictFn (restrictFn f ρ₁) ρ₂`.
Here `composeRestr ρ₁ ρ₂ i = (ρ₁ i).orElse (fun _ => ρ₂ i)` gives `ρ₁`
priority, and `restrictFn f ρ x = f (ρ.extend x)` with
`ρ.extend x i = (ρ i).getD (x i)`.

**Proof.** Immediate from `unfold restrictFn composeRestr Restriction.extend;
aesop`: after unfolding, both sides evaluate `f` at a point whose `i`-th
coordinate is decided by a case split on `ρ₁ i` — if `ρ₁ i = some b` both give
`b`, and if `ρ₁ i = none` both give `(ρ₂ i).getD (x i)`. `aesop` performs that
`Option` case analysis. ∎

**Used in.** Nothing — unused here and elsewhere, and it duplicates verbatim
the already-proved `restrictFn_composeRestr` of
`LMN/Depth3Switching.lean` (there is a third, `private`, copy in
`LMN/RecursiveReduction.lean`).
