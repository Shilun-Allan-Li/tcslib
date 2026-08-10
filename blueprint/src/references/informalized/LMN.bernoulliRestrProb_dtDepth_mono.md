<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: bernoulliRestrProb_dtDepth_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Raising the depth threshold can only lower the failure probability

**Claim.** Let `0 ≤ p ≤ 1`, let `f : (Fin n → Bool) → Bool`, and let
`l₁ ≤ l₂`. Then
`bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > l₂) ≤
bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > l₁)`.

**Proof.** One line: `bernoulliRestrProb_mono p hp hp1 _ _ (fun _ hgt => by
omega)`. The event `dtDepth (restrictFn f ρ) > l₂` implies
`dtDepth (restrictFn f ρ) > l₁` because `l₁ ≤ l₂`, which `omega` discharges, and
monotonicity of the weighted indicator sum does the rest. ∎

A deliberately granular helper: it is the depth-threshold specialization of
`bernoulliRestrProb_mono` (`LMN/GateSwitching.lean`).

**Used in.** Nothing — no other declaration in the repository references it.
