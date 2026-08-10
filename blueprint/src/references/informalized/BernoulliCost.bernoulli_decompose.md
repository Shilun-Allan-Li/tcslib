<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/BernoulliCost.lean :: bernoulli_decompose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli restriction probability is a binomial mixture of fixed-size models

**Claim.** For `p : ℝ` and a decidable predicate `event : Restriction n → Prop`,
`bernoulliRestrProb p event = ∑ k ∈ Finset.range (n + 1), binomialPMF n p k *
fixedSizeRestrProb event k`. That is, conditioning the Bernoulli(`p`) model on
`|ρ⁻¹(⋆)| = k` yields exactly the uniform fixed-size model `R_k`, and the mixing
weights are binomial. (The `0 ≤ p ≤ 1` arguments are named `_hp`/`_hp1` and are
not used.)

**Proof.** Three `have` blocks, then a `convert`.

1. **Counting `R_k`'s support:** for `k ≤ n`,
   `(fixedSizeRestrs n k).card = C(n,k) · 2^(n−k)`. `Finset.card_biUnion`
   (disjointness by `Finset.disjoint_left`) splits the count over which
   `k`-subset is starred, i.e. a sum over `Finset.powersetCard k univ`; each
   summand is `2^(n−k)` by three chained `Finset.card_bij` bijections
   (`freeVars = s` ↔ `Option Bool` functions starred exactly on `s` ↔ `Bool`
   functions trivial on `s` ↔ functions `{i // i ∉ s} → Bool`); then
   `Finset.sum_const`, `Finset.card_powersetCard`, `Finset.card_fin`.
2. **Regrouping the sum:** `bernoulliRestrProb p event` — a sum over all of
   `Restriction n` — equals `∑ k ∈ range (n+1), ∑ ρ ∈ fixedSizeRestrs n k, …`,
   by `Finset.sum_sigma'` and `Finset.sum_bij` along `ρ ↦ ⟨ρ.freeVars.card, ρ⟩`.
   The map lands in range since `ρ.freeVars.card ≤ card univ = n`
   (`Finset.card_le_univ`, `Fintype.card_fin`, `omega`).
3. **Evaluating one block:** for `k ≤ n` the inner sum equals
   `binomialPMF n p k * |filter event (fixedSizeRestrs n k)| /
   |fixedSizeRestrs n k|`. Every `ρ` in the block has the same weight
   `p^k · ((1−p)/2)^(n−k)`, so `Finset.sum_ite` + `Finset.sum_const` give that
   constant times the count of satisfying `ρ`'s; `eq_div_iff` (nonzero by
   `Nat.choose_pos`, `pow_pos`), `push_cast`, `div_pow`, `field_simp` reconcile
   it with `C(n,k) p^k (1−p)^(n−k)` — the `2^(n−k)` from step 1 cancels the one
   in the weights.
4. `convert … using 2` on step 2, rewriting by step 3 and `fixedSizeRestrProb`;
   `ring` closes the residue.

**Remark.** That cancellation is the whole content: the Bernoulli weight is
constant on each level set, so the level-`k` mass is `C(n,k) p^k (1−p)^(n−k)`
and the conditional law is uniform. Needs `set_option maxHeartbeats 800000`.

**Used in.** `bernoulli_restriction_cost`, as the identity that lets the
fixed-size hypothesis be averaged.
