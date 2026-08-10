<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionCardTail.lean :: card_inter_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `|U ∩ J|` as a sum of free-coordinate indicators

**Claim.** For `U : Finset (Fin n)` and a restriction `ρ`, the real number
`((U ∩ ρ.freeVars).card : ℝ)` equals `∑ i ∈ U, (if ρ i = none then 1 else 0)`.
A granular rewriting helper: it puts the counting statistic in additive form so
the two moment lemmas can push expectations through the sum.

**Proof.**

1. `U ∩ ρ.freeVars = U.filter (fun i => ρ i = none)` by `ext i` and
   `simp [Finset.mem_filter, Finset.mem_inter, mem_freeVars]`.
2. Rewrite with that, then `Finset.card_filter` expresses the cardinality as a
   sum of `0/1` naturals.
3. `push_cast` moves the cast inside the sum and `rfl` closes the goal. ∎

**Used in.** `expectation_card_inter` and `expectation_card_inter_sq`.
