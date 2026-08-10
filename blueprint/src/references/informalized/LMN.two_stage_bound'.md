<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: two_stage_bound' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two-stage bound for a composed Bernoulli restriction

**Claim.** Let `0 < p₁ ≤ 1` and `0 < p₂ ≤ 1`, let `E` and `A` be decidable
predicates on `Restriction n`, and let `0 ≤ β`. Suppose that for every `ρ₁` with
`¬A ρ₁` the conditional bound
`bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) ≤ β` holds. Then
`bernoulliRestrProb (p₁ * p₂) E ≤ bernoulliRestrProb p₁ A + β`. Read
probabilistically: `A` is the stage-1 failure event, and conditioned on stage 1
succeeding the stage-2 failure probability is at most `β`.

**Proof.**

1. `rw [restriction_compose_eq]` replaces the left side by
   `∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * bernoulliRestrProb p₂ (fun ρ₂ =>
   E (composeRestr ρ₁ ρ₂))`; its positivity side goals go to `grind`, `linarith`
   and `hp₂`. `add_comm` orients the right side.
2. `h_sum_bound` compares that sum termwise (`gcongr`) with
   `∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * (if A ρ₁ then 1 else β)`: weights are
   nonnegative by `bernoulliRestrWeight_nonneg'`, and after `split_ifs` the
   `A ρ₁` branch uses the trivial bound `bernoulliRestrProb_le_one'` while the
   `¬A ρ₁` branch uses the hypothesis `h_bound`.
3. `simp [bernoulliRestrProb, Finset.sum_ite]` splits that sum into the `A`
   part — which is exactly `bernoulliRestrProb p₁ A` — and the `¬A` part.
4. The `¬A` part is `β * ∑_{¬A ρ₁} bernoulliRestrWeight p₁ ρ₁`
   (`Finset.sum_mul`), and `Finset.sum_le_sum_of_subset_of_nonneg` together with
   `bernoulliRestrWeight_sum_one` bounds that partial weight sum by `1`, so
   `mul_le_of_le_one_left hβ` gives `≤ β`. ∎

**Used in.** `circuit_reduction_ind_step`, instantiated with
`p₁ = composedDelta w l (d-1)` and `p₂ = 1 / (40 * l)` (their product being the
goal parameter by `composedDelta_step_right`), `A ρ₁` = "some child of the root
gate still has `dtDepth > l`", and `β = (1/2)^t + exp(-n/(120l))`. Note the
statement is identical to `two_stage_bound` in `LMN/Depth3Switching.lean`; this
is a re-proved duplicate.
