<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: bernoulliRestrWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Weight of a restriction in the Bernoulli(p) model

**Definition.** For a real parameter `p` and a restriction
`ρ : Restriction n = Fin n → Option Bool`,

```
bernoulliRestrWeight p ρ = p ^ ρ.freeVars.card * ((1 - p) / 2) ^ (n - ρ.freeVars.card)
```

where `ρ.freeVars` is the finset of coordinates with `ρ i = none`. This is the
probability of drawing exactly `ρ` when each of the `n` variables is
independently left free with probability `p` and otherwise fixed to `true` or
`false` with probability `(1 - p) / 2` each: every free variable contributes a
factor `p`, every fixed variable a factor `(1 - p) / 2`.

Note the definition is unconditional in `p` — it is a real-valued formula, not
a probability measure; that it is a genuine distribution is exactly the content
of `bernoulliRestrWeight_nonneg'` (for `0 ≤ p ≤ 1`) and
`bernoulliRestrWeight_sum_one`.

**Used in.** `bernoulliRestrProb`, and through it the random-restriction
probability estimates of the switching-lemma development. Declared inside
`noncomputable section` with `open Classical`.
