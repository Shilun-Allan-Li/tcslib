<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: varWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Per-variable weight in the Bernoulli restriction model

**Definition.** `varWeight (p : ℝ) : Option Bool → ℝ` is defined by pattern
match on a single coordinate's value:

- `varWeight p none = p` — the coordinate is left free;
- `varWeight p (some _) = (1 - p) / 2` — the coordinate is fixed to `false` or
  to `true`, each with half of the remaining mass.

**Remark.** This is the one-coordinate marginal of the Bernoulli(`p`) model:
the three outcomes have total weight `p + 2·((1-p)/2) = 1`. Nothing constrains
`p` to `[0,1]` in the definition, so the weights are real numbers, not
necessarily a probability distribution, until a hypothesis `0 ≤ p ≤ 1` is
supplied by the caller.

**Used in.** `bernoulliRestrWeight_eq_prod` (the global weight is the product of
these over all coordinates), `varWeight_compose_sum`, and reused in
`RestrictionFourier.lean` (`sum_varWeight_localFactor` and the
product-of-sums factorization there).
