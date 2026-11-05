<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: bernoulliRestrProb_subset_freeVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Free-set marginal: `Pr[T ⊆ J] = p^{|T|}`

**Claim.** For every `p : ℝ` and `T : Finset (Fin n)`, the Bernoulli(`p`)
restriction probability that all of `T` is free,
`bernoulliRestrProb p (fun ρ => T ⊆ ρ.freeVars)`, equals `p ^ T.card`. No
hypotheses on `p` are needed — the identity is a formal computation with the
weights, valid for arbitrary real `p`.

**Proof.**

1. `unfold bernoulliRestrProb` and rewrite each indicator by
   `indicator_subset_eq_prod T ρ`, turning the sum into a Bernoulli-weighted
   sum of per-coordinate products.
2. Apply the factorization `sum_bernoulli_prod p` with local factor
   `fun i v => if i ∈ T then (if v = none then 1 else 0) else 1`, producing a
   product over `i` of one-variable sums over `v : Option Bool`.
3. Each such sum is `if i ∈ T then p else 1`: split on `i ∈ T` and unfold
   `varWeight` (`by_cases hiT ... <;> simp [varWeight, hiT] <;> ring`), using
   `varWeight p none = p`.
4. The product of these factors is `p ^ T.card` by
   `Finset.prod_ite_mem`, `Finset.univ_inter` and `Finset.prod_const`. ∎

**Used in.** `expectation_free_indicator` (case `T = {i}`) and
`expectation_free_indicator_pair` (case `T = {i, j}`), the two moment
computations of this file.
