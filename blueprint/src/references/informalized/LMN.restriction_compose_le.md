<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCompose.lean :: restriction_compose_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Composition inequality: replace the second stage by an existential

**Claim.** Let `0 < p ≤ 1`, `0 < q ≤ 1` and `event : Restriction n → Prop` be
decidable. Then

`bernoulliRestrProb (p * q) event ≤ bernoulliRestrProb p (fun ρ₁ => ∃ ρ₂, event (composeRestr ρ₁ ρ₂))`.

The Bernoulli(`p*q`) probability of an event is at most the Bernoulli(`p`)
probability that *some* second-stage restriction makes it hold.

**Proof.** Expand by the equality version and bound each inner probability by an
indicator.

1. `rw [restriction_compose_eq p q hp hp1 hq hq1 event]` turns the left side into
   `∑ ρ₁, bernoulliRestrWeight p ρ₁ * bernoulliRestrProb q (fun ρ₂ => event (composeRestr ρ₁ ρ₂))`.
2. `Finset.sum_le_sum` with `mul_le_mul_of_nonneg_left` and
   `bernoulliRestrWeight_nonneg' p hp.le hp1 ρ₁` reduces to bounding the inner
   factor termwise; the comparison function
   `fun ρ₁ => if ∃ ρ₂, event (composeRestr ρ₁ ρ₂) then 1 else 0` is supplied to
   the `refine'` metavariable afterwards by `any_goals exact …`.
3. **Inner bound**, by `split_ifs <;> simp_all +decide [bernoulliRestrProb]`:
   - if some `ρ₂` works, the target is `bernoulliRestrProb q … ≤ 1`, i.e.
     `bernoulliRestrProb_le_one' q hq.le hq1 _` (matched up by `convert … using 1`
     and `Finset.sum_congr rfl fun _ _ => by aesop`);
   - if none works, every summand's indicator is `0`, so the inner probability
     is `0`.
4. The resulting indicator sum *is* the right-hand side by definition:
   `unfold bernoulliRestrProb; aesop`.

**Remark.** Unlike `restriction_compose_eq`, this direction really uses the
hypotheses: `0 ≤ p ≤ 1` for weight nonnegativity in step 2 and `0 ≤ q ≤ 1` for
the `≤ 1` bound in step 3. Decidability of the existential comes from the file's
local `Classical.propDecidable` instance.

**Used in.** No other declaration cites it; it is the module's advertised
convenience corollary for union-bound style arguments.
