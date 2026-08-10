<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: full_iterative_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Summed per-layer failure plus a final term

**Claim.** Let `layerSize : Fin m → ℕ` with `∑ i, layerSize i ≤ s`, let
`α β : ℝ` with `0 ≤ α`, and let `per_layer : Fin m → ℝ` satisfy
`per_layer i ≤ layerSize i * α` for every `i`, and `final ≤ β`. Then
`(∑ i, per_layer i) + final ≤ s * α + β`.

**Proof.** One line: `add_le_add` applied to
`multi_stage_failure_bound m layerSize s h_sum α hα per_layer h_per`, which
supplies `∑ i, per_layer i ≤ s * α`, and to `h_final : final ≤ β`. ∎

Despite its name this is a purely arithmetic bookkeeping statement — no
circuits, restrictions, or probabilities appear. It is the shape the LMN layer
accounting would take (`m` layers each contributing `layerSize i * α`, plus one
final `β` term), packaged for reuse.

**Used in.** Nothing — no other declaration in the repository references it; the
actual induction in this file (`circuit_reduction_ind_step`) does its
per-children accounting with `List.foldr` bounds rather than through this lemma.
