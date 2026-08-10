<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: dtDepth_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Decision-tree depth is invariant under negation

**Claim.** For any `f : (Fin n → Bool) → Bool`,
`dtDepth (fun x => !(f x)) = dtDepth f`, where
`dtDepth f = Nat.find (fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)`.

**Proof.** By `le_antisymm`, with the two directions symmetric.

1. (`≤`) Unfold `dtDepth` and use `Nat.find_le`: it suffices to exhibit a tree of
   depth `≤ dtDepth f` computing `!f`.
2. `Nat.find_spec` (with the same termination witness `buildFullDTree` used in the
   definition of `dtDepth`) supplies `T` with `T.depth ≤ dtDepth f` and
   `∀ x, T.eval x = f x`.
3. `T.negateLeaves` is the witness: `DecisionTree.negateLeaves_depth` keeps the
   depth and `DecisionTree.negateLeaves_eval` gives
   `T.negateLeaves.eval x = !(T.eval x) = !(f x)`.
4. The reverse inequality is the identical argument starting from a tree for
   `fun x => !(f x)` and negating its leaves. ∎

One remark: since negation is an involution on leaves, no arithmetic on depths is
needed — the same tree shape works in both directions.

**Used in.** `IsBadRestriction_neg`, hence in `switching_lemma_cnf`, which derives
the CNF switching lemma from the DNF one by De Morgan duality.
