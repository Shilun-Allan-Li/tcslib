<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: exp_neg_eventually_small -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The tail term `e^{−mp/3}` is eventually below any `ε`

**Claim.** For `p : ℝ` with `0 < p` and `ε : ℝ` with `0 < ε`, there is `N : ℕ`
such that `Real.exp (-(m · p / 3)) < ε` for all `m : ℕ` with `N ≤ m`.

**Proof.** One `simpa` over a composed limit — no case analysis.

1. `tendsto_natCast_atTop_atTop.atTop_mul_const hp` gives `m · p → ∞`,
   `Filter.Tendsto.atTop_div_const (by positivity)` divides by `3`,
   `Filter.tendsto_neg_atTop_atBot` negates to `−∞`, and
   `Real.tendsto_exp_atBot` composes to `exp (−(m p / 3)) → 0` along
   `atTop`.
2. `.eventually (gt_mem_nhds hε)` says the values are eventually in `{x | x < ε}`;
   `Filter.eventually_atTop.mp` extracts the threshold `N` and the bound for all
   `m ≥ N`.
3. `simpa [neg_div]` reconciles `−(m p / 3)` with the form produced by the limit
   composition.

**Used in.** `bernoulli_restriction_asymptotic`, which picks its `N` from here.
