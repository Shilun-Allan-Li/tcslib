<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/BernoulliRestriction.lean :: bernoulliRestrWeight_sum_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli restriction weights sum to one

**Claim.** For any `p : ℝ`, `∑ ρ : Restriction n, bernoulliRestrWeight p ρ = 1`.
The two hypotheses `0 ≤ p` and `p ≤ 1` are present in the signature but bound
as `_hp` and `_hp1`, i.e. unused — the identity is an algebraic one, valid for
every real `p`.

**Proof.** The weight of `ρ` depends only on `ρ.freeVars.card`, so the sum over
`Restriction n = Fin n → Option Bool` factors coordinatewise.

1. `have h_prod_sum` rewrites the sum, with `freeVars` spelled out as
   `Finset.univ.filter (fun i => ρ i = none)`, as the product
   `∏ i : Fin n, ∑ ρ_i : Option Bool, (if ρ_i = none then p else (1 - p) / 2)`.
   This is `Finset.prod_sum` (distributing a product of sums into a sum over
   functions) followed by `Finset.sum_bij` with the bijection
   `fun ρ _ => fun i _ => ρ i` between plain and dependent function encodings;
   the four bijection obligations go by `simp +decide`, `funext_iff`, and an
   explicit inverse. The per-summand match uses `Finset.prod_ite` together with
   `Finset.filter_not` / `Finset.card_sdiff` to turn the product over the two
   filter blocks into the `p ^ k * ((1-p)/2) ^ (n - k)` shape (`div_pow` for the
   halved factor).
2. `convert h_prod_sum using 1` reduces to two goals. The left one is
   definitional: `unfold bernoulliRestrWeight` then
   `congr; ext; simp +decide [Restriction.freeVars]`.
3. The right one evaluates the inner sum over `Option Bool`: by
   `Finset.sum_ite`, `Finset.filter_eq'`, `Finset.filter_ne'` it is
   `p + 2 * ((1 - p) / 2)`, which is `1` by `ring` (`h1`), and `1 ^ n = 1` by
   `one_pow`. ∎

**Used in.** `bernoulliRestrProb_le_one'` (the final `_ = 1` step of its
`calc`), and as the normalization fact wherever the Bernoulli model is treated
as a distribution, e.g. `LMN/CircuitLayerReduction.lean`.
