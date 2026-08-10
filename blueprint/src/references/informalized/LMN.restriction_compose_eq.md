<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: restriction_compose_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Bernoulli restrictions compose (equality form)

**Claim.** Let `p q : ℝ` with `0 < p ≤ 1` and `0 < q ≤ 1`, and let
`event : Restriction n → Prop` be decidable. Then

`bernoulliRestrProb (p * q) event = ∑ ρ₁ : Restriction n, bernoulliRestrWeight p ρ₁ * bernoulliRestrProb q (fun ρ₂ => event (composeRestr ρ₁ ρ₂))`.

A Bernoulli(`p`) restriction followed by a Bernoulli(`q`) restriction on the
still-free variables has the same event probabilities as a single
Bernoulli(`p*q`) restriction.

**Proof.** `unfold bernoulliRestrProb` on both sides, then rewrite the
Bernoulli(`p*q`) weight of each `ρ` as a fiber sum and swap the order of
summation.

1. **`h_sum`:** for each `ρ`,
   `bernoulliRestrWeight (p*q) ρ * [event ρ] = ∑ ρ₁, ∑ ρ₂, bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ * (if composeRestr ρ₁ ρ₂ = ρ then [event ρ] else 0)`.
   The weight identity itself is `compose_fiber_weight_eq p q ρ` (used via
   `convert … |> Eq.symm using 1`); `split_ifs <;> simp +decide [*, Finset.sum_ite]`
   then handles the two cases of `[event ρ]`, the `event`-false case making both
   sides `0`.
2. `simp +decide only [h_sum, Finset.mul_sum _ _ _]` substitutes this into the
   outer sum over `ρ`, giving a triple sum over `(ρ, ρ₁, ρ₂)`.
3. `rw [Finset.sum_comm, Finset.sum_congr rfl]`, then per `ρ₁` another
   `rw [Finset.sum_comm]` and `simp +decide`: the innermost sum over `ρ` has a
   single surviving term `ρ = composeRestr ρ₁ ρ₂`, which reassembles the
   right-hand side.

**Remark.** All four hypotheses are named with a leading underscore
(`_hp`, `_hp1`, `_hq`, `_hq1`) and are genuinely unused — the statement is a
purely algebraic identity between weight sums, valid for arbitrary real `p`, `q`.
The bounds are kept so callers read it as a probability statement.

**Used in.** `restriction_compose_le`, and downstream in `Depth3Switching.lean`
(rewriting `bernoulliRestrProb (p₁ * p₂) E` into a two-stage sum) and in the
narrative of `IterativeReduction.lean`.
