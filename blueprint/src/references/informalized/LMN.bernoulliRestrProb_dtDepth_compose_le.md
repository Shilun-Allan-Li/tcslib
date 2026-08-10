<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity.lean :: bernoulliRestrProb_dtDepth_compose_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A stronger Bernoulli restriction lowers the deep-tree probability

**Claim.** Let `f : (Fin n → Bool) → Bool`, `t : ℕ`, and `p₁, p₂ : ℝ` with
`0 < p₁ ≤ 1` and `0 < p₂ ≤ 1`. Then
`bernoulliRestrProb (p₁ * p₂) (fun ρ => dtDepth (restrictFn f ρ) > t) ≤
bernoulliRestrProb p₁ (fun ρ => dtDepth (restrictFn f ρ) > t)`.
Since `p₁ * p₂ ≤ p₁` keeps fewer variables free, the event "the restricted
function still needs depth more than `t`" becomes no more likely.

**Proof.** Split the `p₁ * p₂` restriction into two stages and compare termwise.

1. `rw [restriction_compose_eq p₁ p₂ …]` rewrites the left side as
   `∑_{ρ₁} bernoulliRestrWeight p₁ ρ₁ ·
   bernoulliRestrProb p₂ (fun ρ₂ => dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) > t)`.
2. `Finset.sum_le_sum` reduces to a per-`ρ₁` inequality against the right-hand
   summand `bernoulliRestrWeight p₁ ρ₁ * (if dtDepth (restrictFn f ρ₁) > t then 1 else 0)`.
   Case split with `by_cases h : dtDepth (restrictFn f ρ₁) > t`.
3. If `h` holds, the right-hand indicator is `1`, and a `calc` bounds the inner
   probability by `1` via `bernoulliRestrProb_le_one'`, multiplied on the left by
   the nonnegative weight (`mul_le_mul_of_nonneg_left`,
   `bernoulliRestrWeight_nonneg'`).
4. If `h` fails (`push_neg`), the inner probability is *exactly* `0`: unfolding
   `bernoulliRestrProb` and applying `Finset.sum_eq_zero`, each `ρ₂` term has a
   false indicator because `dtDepth_composeRestr_le f ρ₁ ρ₂` chained with `h`
   gives `dtDepth (restrictFn f (composeRestr ρ₁ ρ₂)) ≤ t`. The left side is then
   `0` (`mul_zero`) and the right side is nonneg (`mul_nonneg`).

**Note.** The declaration is currently unused elsewhere in the library and its
preceding comment block is a plain `/- … -/` rather than a docstring; it records
the monotonicity that lets the multi-stage argument keep a single parameter.
