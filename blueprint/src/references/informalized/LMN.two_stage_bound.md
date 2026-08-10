<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: two_stage_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two-stage restriction bound

**Claim.** Let `0 < p₁ ≤ 1`, `0 < p₂ ≤ 1`, let `E, A : Restriction n → Prop` be
decidable predicates, and `0 ≤ β`. If for every `ρ₁` with `¬A ρ₁` we have
`bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂)) ≤ β`, then
`bernoulliRestrProb (p₁ * p₂) E ≤ bernoulliRestrProb p₁ A + β`. So `A` is the
"stage-1 failure" event and `β` the conditional stage-2 bound.

**Proof.**

1. `h_eq`: `restriction_compose_eq` (with `p₁·p₂` split, side goals by `linarith`
   and `grind`) rewrites the composed probability as
   `∑ ρ₁, bernoulliRestrWeight p₁ ρ₁ * bernoulliRestrProb p₂ (fun ρ₂ => E (composeRestr ρ₁ ρ₂))`.
2. `h_sum_bound`: bound each summand by `bernoulliRestrWeight p₁ ρ₁ * (if A ρ₁ then 1 else β)`
   using `gcongr`, with weight nonnegativity from `bernoulliRestrWeight_nonneg'`
   and the two cases `bernoulliRestrProb_le_one'` (when `A ρ₁`) and `h_bound`
   (when `¬A ρ₁`).
3. `simp [Finset.sum_ite, bernoulliRestrProb]` splits that sum into the `A`-part,
   which is literally `bernoulliRestrProb p₁ A`, and the `¬A`-part; `← Finset.sum_mul`
   factors `β` out of the latter.
4. The remaining weight sum over the `¬A` fibre is at most the total weight `1`
   (`Finset.sum_le_sum_of_subset_of_nonneg` into `bernoulliRestrWeight_sum_one`),
   so `mul_le_of_le_one_left hβ` gives `β · (…) ≤ β`. ∎

**Used in.** `depth3_switching_bound`, instantiated with `A ρ₁ = ∃ i, dtDepth (restrictFn (gates i).eval ρ₁) > l`
and `β = (1/2)^t + exp(-n·p₂/3)`. It is the only sorry-free named result in this
file's dependency chain, and is independent of the CNF-cleanup lemmas.
