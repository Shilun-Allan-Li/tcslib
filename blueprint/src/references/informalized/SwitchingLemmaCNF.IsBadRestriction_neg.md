<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: IsBadRestriction_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Badness of a restriction is invariant under negation

**Claim.** For `f : (Fin n → Bool) → Bool`, `d : ℕ` and a restriction `ρ`,
`IsBadRestriction (fun x => !(f x)) d ρ ↔ IsBadRestriction f d ρ`. Unfolding
`IsBadRestriction`, this says `dtDepth (restrictFn (¬f) ρ) > d` iff
`dtDepth (restrictFn f ρ) > d`.

**Proof.** Immediate from
`simp only [IsBadRestriction, restrictFn_neg, dtDepth_neg]`: `restrictFn_neg`
pushes the negation through the restriction, and `dtDepth_neg` says decision-tree
depth is unchanged by negating the function (negate a tree's leaves with
`DecisionTree.negateLeaves` — same depth, complemented value).

**Used in.** The De Morgan transfer from the DNF switching lemma to the CNF one
(`switching_lemma_cnf` uses `restrictFn_neg` and `dtDepth_neg` directly at the
same step); this lemma packages the equivalence in `IsBadRestriction` form for
reuse.
