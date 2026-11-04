<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: bernoulliRestrWeight_eq_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Bernoulli restriction weight factors over coordinates

**Claim.** For every `p : ℝ` and `ρ : Restriction n`,

`bernoulliRestrWeight p ρ = ∏ i : Fin n, varWeight p (ρ i)`,

i.e. the closed form `p ^ |ρ.freeVars| * ((1-p)/2) ^ (n - |ρ.freeVars|)` equals
the coordinatewise product of `varWeight`s. No hypothesis on `p`.

**Proof.** Split the product at the free/fixed partition, then count.

1. **`h_split`:** `∏ i, varWeight p (ρ i) = (∏ i ∈ ρ.freeVars, p) * (∏ i ∈ univ \ ρ.freeVars, (1-p)/2)`.
   Obtained by `rw [← Finset.prod_sdiff (Finset.subset_univ ρ.freeVars)]` and
   `mul_comm`, then matching the two factors with
   `congrArg₂ _ (Finset.prod_congr rfl …) (Finset.prod_congr rfl …)` and
   `simp_all +decide [Restriction.freeVars]`: on `ρ.freeVars` the value is
   `none` so `varWeight p (ρ x) = p` (`rfl`), and off it `ρ x = some _` so the
   weight is `(1-p)/2` (`cases h : ρ x <;> aesop`).
2. The two constant products collapse to powers with exponents
   `|ρ.freeVars|` and `n - |ρ.freeVars|` — `simp_all +decide [Finset.card_sdiff]`
   supplies the complement's cardinality.
3. `unfold bernoulliRestrWeight; ring_nf`, then the normal forms are reconciled
   by `rw [show (1 / 2 + p * (-1 / 2)) = (1 - p) / 2 by ring]`, `rw [div_pow]`,
   `ring_nf!` and `norm_num` — bookkeeping only, `ring_nf` having pushed the
   `(1-p)/2` base into an expanded form.

**Used in.** `compose_fiber_weight_eq` (both to expand the summands and to close
the goal at parameter `p * q`) and, outside this file, `RestrictionFourier.lean`.
