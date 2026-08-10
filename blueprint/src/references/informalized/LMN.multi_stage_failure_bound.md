<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean :: multi_stage_failure_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Per-layer failure bounds sum to `s · α`

**Claim.** Let `layer_size : Fin m → ℕ` with `∑ i, layer_size i ≤ s`, let
`α : ℝ` with `0 ≤ α`, and let `failure_bound : Fin m → ℝ` satisfy
`failure_bound i ≤ (layer_size i : ℝ) * α` for every `i`. Then
`∑ i, failure_bound i ≤ (s : ℝ) * α`.

**Proof.** A one-step chain (`le_trans`) with no case analysis:

1. `Finset.sum_le_sum fun i _ => h_bound i` gives
   `∑ i, failure_bound i ≤ ∑ i, (layer_size i : ℝ) * α`.
2. `Finset.sum_mul` factors the right-hand sum as `(∑ i, (layer_size i : ℝ)) * α`,
   and `mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h_sum) hα` replaces the
   cast sum of layer sizes by `(s : ℝ)`, using `0 ≤ α`.

**Remark.** Purely arithmetic — it is the union-bound bookkeeping of Step 9,
where `∑ layer_size i ≤ s` holds because every gate belongs to exactly one layer;
nothing about circuits or restrictions enters the statement.

**Used in.** `full_iterative_bound` in `CircuitLayerReduction.lean`, added to a
separate final-stage bound `β` to give the total error `s · α + β`.
