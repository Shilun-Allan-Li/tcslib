<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: compose_fiber_weight_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fiber weight of the composition map

**Claim.** For all `p q : ℝ` and every `σ : Restriction n`,

`∑ ρ₁, ∑ ρ₂, bernoulliRestrWeight p ρ₁ * bernoulliRestrWeight q ρ₂ * [composeRestr ρ₁ ρ₂ = σ] = bernoulliRestrWeight (p * q) σ`,

i.e. the total `p ⊗ q` weight of the fiber of `composeRestr` over `σ` is the
Bernoulli(`p*q`) weight of `σ`. No hypothesis on `p`, `q`.

**Proof.** Lift the double sum to a sum over coordinatewise pairs, then exchange
sum and product coordinate by coordinate.

1. **`h_double_sum`:** rewrite the double sum as
   `∑ g : Fin n → Option Bool × Option Bool, ∏ i, (varWeight p (g i).1 * varWeight q (g i).2 * [(g i).1.orElse (fun _ => (g i).2) = σ i])`.
   - Inner step: each summand becomes such a product, via
     `bernoulliRestrWeight_eq_prod`, `Finset.prod_mul_distrib` and
     `Finset.prod_ite`, with `split_ifs <;> simp_all +decide [Finset.ext_iff, funext_iff, composeRestr]`
     matching the global indicator `[composeRestr ρ₁ ρ₂ = σ]` against the
     product of per-coordinate indicators.
   - Outer step: `rw [← Finset.sum_product']` then `Finset.sum_bij` with
     `(ρ₁, ρ₂) ↦ fun i => (ρ₁ i, ρ₂ i)` — the currying bijection
     `(Fin n → A) × (Fin n → B) ≃ (Fin n → A × B)`, injectivity by
     `funext_iff`/`Prod.ext_iff`.
2. **`h_per_variable`:** for each `i`,
   `∑ g : Option Bool × Option Bool, varWeight p g.1 * varWeight q g.2 * [g.1.orElse (fun _ => g.2) = σ i] = varWeight (p*q) (σ i)`
   — `Fintype.sum_prod_type` turns the pair sum into the iterated sum handled by
   `varWeight_compose_sum p q (σ i)`.
3. `convert Finset.prod_congr rfl fun i _ => h_per_variable i using 1` reduces to
   two goals: the sum/product exchange `Finset.prod_sum` plus a second
   `Finset.sum_bij` (`g ↦ fun i _ => g i`, dropping the membership argument),
   and the closing rewrite `bernoulliRestrWeight_eq_prod (p * q) σ`.

**Used in.** `restriction_compose_eq`.
