<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: bernoulli_restriction_asymptotic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Asymptotically the Bernoulli model costs nothing

**Claim.** Fix `0 < p ≤ 1`, `0 < w`, `0 < s` and `ε > 0`. Then there exists
`N : ℕ` such that for every `nn ≥ N` with `0 < nn` and every decidable
`event : Restriction nn → Prop` satisfying
`fixedSizeRestrProb event k ≤ (5 k w / nn) ^ s` for all `k ≤ nn`, we have
`bernoulliRestrProb p event ≤ (10 p w) ^ s + ε`. The threshold `N` is uniform in
the event — it is chosen before `event` is quantified.

**Proof.** Two lines.

1. `obtain ⟨N, hN⟩ := exp_neg_eventually_small p hp ε hε` supplies `N` with
   `Real.exp (-(m · p / 3)) < ε` for all `m ≥ N`.
2. For that `N` and any `nn`, `event`, a `calc`:
   `bernoulliRestrProb p event ≤ (10 p w)^s + exp (-(nn · p / 3))` by
   `bernoulli_restriction_cost hn_pos p hp hp1 w s hw hs event h_fixed`, then
   `≤ (10 p w)^s + ε` by `linarith [hN nn hn]`.

**Remark.** This is the headline statement of the file: the additive `e^{−np/3}`
of `bernoulli_restriction_cost` is absorbed into an arbitrary `ε`, leaving
`(10pw)^s` as the only asymptotic content, so switching lemma bounds proved in
the fixed-size model `R_k` may be used in the Bernoulli model `R_p`.
