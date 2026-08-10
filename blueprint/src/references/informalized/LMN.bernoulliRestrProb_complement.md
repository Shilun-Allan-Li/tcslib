<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: bernoulliRestrProb_complement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli restriction probabilities of an event and its complement sum to 1

**Claim.** For `p : ℝ` with `0 ≤ p ≤ 1` and any decidable predicate
`A : Restriction n → Prop`,

`bernoulliRestrProb p A + bernoulliRestrProb p (fun ρ => ¬ A ρ) = 1`.

**Proof.** Three rewrites.

1. `unfold bernoulliRestrProb`: both sides are sums over all restrictions of
   `bernoulliRestrWeight p ρ` times an indicator.
2. `← Finset.sum_add_distrib` merges the two sums into one, and
   `Finset.sum_congr rfl … (by aesop)` evaluates the merged summand: exactly one
   of `A ρ`, `¬ A ρ` holds, so the two indicators contribute
   `weight * 1 + weight * 0 = weight` either way.
3. `bernoulliRestrWeight_sum_one p hp hp1` gives that the total weight is `1`.

**Anomaly.** Declared but never used anywhere in the repository — even though the
`sorry` in the next declaration of the same file,
`one_step_reduction_with_compression`, is annotated
`TODO: needs bernoulliRestrProb complement lemma: P(E) ≥ 1 - P(¬E)`, i.e. this
lemma is the missing ingredient for the very proof it sits next to. (The
neighbouring `one_step_dtDepth_bound` proves the same complement identity
inline, as a `have h_total`.)
