<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: bernoulliRestrProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Probability of an event under a Bernoulli(p) random restriction

**Definition.** Given `p : ℝ` and a predicate `event : Restriction n → Prop`
with `[DecidablePred event]`,

```
bernoulliRestrProb p event = ∑ ρ : Restriction n, bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)
```

i.e. the `bernoulliRestrWeight`-weighted count of the restrictions satisfying
`event`, summed over the whole finite type `Restriction n = Fin n → Option Bool`.
The indicator is written as an `if _ then 1 else 0` rather than via
`Finset.filter`, which is what lets `Finset.sum_le_sum` be applied pointwise in
the bound below.

As with `bernoulliRestrWeight`, no hypothesis on `p` is imposed by the
definition; `0 ≤ p ≤ 1` enters only in the lemmas.

**Used in.** `bernoulliRestrProb_le_one'` (it is at most `1` when `0 ≤ p ≤ 1`),
and thereafter as the probability functional in which switching-lemma failure
probabilities are stated.
