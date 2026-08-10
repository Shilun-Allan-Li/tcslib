<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: bernoulliRestrProb_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Monotonicity of Bernoulli restriction probability

**Claim.** Fix `p : ℝ` with `0 ≤ p ≤ 1` and two decidable predicates `A B :
Restriction n → Prop`. If `A ρ → B ρ` for every restriction `ρ`, then
`bernoulliRestrProb p A ≤ bernoulliRestrProb p B`. (Here
`bernoulliRestrProb p A = ∑ ρ, bernoulliRestrWeight p ρ * (if A ρ then 1 else 0)`,
so this is monotonicity of a weighted indicator sum, not a general measure-theoretic
statement.)

**Proof.**

1. `unfold bernoulliRestrProb` turns the goal into an inequality between two sums
   over all `ρ : Restriction n`; `Finset.sum_le_sum` reduces it to a termwise
   comparison, so fix `ρ`.
2. `by_cases ha : A ρ`. If `A ρ` holds then `B ρ` holds by `h ρ ha`, both
   indicators are `1`, and the two terms are equal — `simp [ha, h ρ ha]`.
3. If `A ρ` fails the left term is `0`, so it suffices that the right term is
   nonnegative: `split_ifs` and `bernoulliRestrWeight_nonneg' p hp hp1 ρ` supply
   `0 ≤ bernoulliRestrWeight p ρ` (this is where `0 ≤ p ≤ 1` is used). ∎

**Used in.** The workhorse for every event-weakening step in this file
(`switching_bernoulli_gate_to_cnf`, `switching_bernoulli_gate_to_dnf_from_cnf`,
`layer2_cnf_replaceability_union_bound`) and in
`LMN/CircuitLayerReduction.lean`.
