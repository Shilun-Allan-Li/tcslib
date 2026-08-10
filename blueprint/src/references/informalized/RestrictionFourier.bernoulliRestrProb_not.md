<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: bernoulliRestrProb_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Complement rule for Bernoulli-restriction probabilities

**Claim.** For `0 ≤ p ≤ 1` and any decidable predicate
`event : Restriction n → Prop`,
`bernoulliRestrProb p (fun ρ => ¬ event ρ) = 1 - bernoulliRestrProb p event`.

**Proof.**

1. Show the two probabilities add to `1` (`hsum`): after
   `unfold bernoulliRestrProb`, combine the sums (`← Finset.sum_add_distrib`);
   termwise, `w ρ * ind(¬event ρ) + w ρ * ind(event ρ) = w ρ` by `by_cases h :
   event ρ <;> simp [h]`.
2. The remaining sum `∑ ρ, bernoulliRestrWeight p ρ` is `1` by
   `bernoulliRestrWeight_sum_one p hp0 hp1` — this is the only place the
   hypotheses on `p` are used.
3. `linarith` rearranges `A + B = 1` into `A = 1 - B`. ∎

**Used in.** `bernoulliRestrProb_card_inter_ge`. The file docstring records that
this is the general lemma flagged as missing by the `sorry` in
`LMN/CircuitCompression.lean`; that `sorry` is still open (see report).
