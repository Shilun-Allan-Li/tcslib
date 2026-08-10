<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/IterativeReduction.lean :: bernoulliRestrProb_union_bound_fin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Finite union bound for Bernoulli restriction probabilities

**Claim.** Let `0 ≤ p ≤ 1`, `m : ℕ`, and `A : Fin m → Restriction n → Prop` a
family of decidable events. Then
`bernoulliRestrProb p (fun ρ => ∃ i, A i ρ) ≤ ∑ i, bernoulliRestrProb p (A i)`.
This is the ordinary union bound, stated for the weighted sum
`bernoulliRestrProb p E = ∑_ρ bernoulliRestrWeight p ρ * (if E ρ then 1 else 0)`.

**Proof.**

1. Unfold both sides (`simp +decide only [bernoulliRestrProb]`) and swap the
   order of summation on the right (`rw [Finset.sum_comm]`), so both sides are
   sums over `ρ`.
2. `gcongr` reduces to the per-`ρ` inequality
   `w ρ * (if ∃ i, A i ρ then 1 else 0) ≤ ∑ i, w ρ * (if A i ρ then 1 else 0)`,
   with `w ρ = bernoulliRestrWeight p ρ`.
3. `split_ifs <;> norm_num`. In the case where some `A i ρ` holds, `obtain` the
   witness `i` and bound `w ρ` by the single `i`-th summand using
   `Finset.single_le_sum`; the required nonnegativity of every summand comes from
   `bernoulliRestrWeight_nonneg' p hp hp1`.
4. In the case where no `A i ρ` holds, the left side is `0` and the right side is
   a sum of nonnegative terms (`Finset.sum_nonneg`, each term closed by
   `positivity` or again `bernoulliRestrWeight_nonneg'`).

**Used in.** `bernoulliRestrProb_list_union_bound` in
`CircuitLayerReduction.lean`, which reindexes a `List (Circuit n)` through
`Fin cs.length` to bound "some gate at this layer fails" by the sum of the
per-gate failure probabilities — Step 9 of the LMN argument.
