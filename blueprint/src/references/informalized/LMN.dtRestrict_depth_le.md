<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity.lean :: dtRestrict_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restricting a decision tree cannot increase its depth

**Claim.** For every `T : DecisionTree n` and every `ρ : Restriction n`,
`(dtRestrict T ρ).depth ≤ T.depth`. No hypotheses on `ρ` — it may fix any set of
variables, including all or none of them.

**Proof.** Structural induction on `T` (`induction'`).

1. Leaf case: `dtRestrict (.leaf b) ρ = .leaf b`, so the two depths are literally
   equal (`rfl`).
2. Branch case `.branch var lo hi`: case split on the value of `ρ var`
   (`cases h : ρ lo <;> simp_all +decide [dtRestrict]`; note the `induction'`
   name list shifts, so the tactic's `lo` is the query variable).
   - `ρ var = none`: the node survives, and both sides are
     `1 + max (…) (…)`, so the two subtree induction hypotheses combine via
     `Nat.add_le_add_left (max_le_max ihhi ‹_›) _`.
   - `ρ var = some b`: the node is deleted, so we must compare a restricted
     subtree against `1 + max lo.depth hi.depth`. Splitting on `b`
     (`cases ‹Bool›`) and unfolding `DecisionTree.depth`, each case is the
     induction hypothesis chained with the arithmetic fact that a subtree depth
     is at most `1 + max`, discharged by `le_trans … (by omega)`.

**Used in.** `dtDepth_restrictFn_le'`, where it turns a depth bound for an
optimal tree computing `f` into a depth bound for its restriction.
