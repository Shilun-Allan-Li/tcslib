<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: DecisionTree.negateLeaves_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Negating the leaves does not change the depth

**Claim.** For every decision tree `T : DecisionTree n`,
`T.negateLeaves.depth = T.depth`.

**Proof.** Induction on `T` (`induction T with`); `negateLeaves` only rewrites
leaf labels, so the branching skeleton — and hence `DecisionTree.depth` — is
untouched.

1. **Leaf**: both depths are `0` (`simp [negateLeaves, DecisionTree.depth]`).
2. **Branch** `.branch v lo hi`: `depth = 1 + max lo.depth hi.depth` on both
   sides, closed by `simp [negateLeaves, DecisionTree.depth, ih_lo, ih_hi]`.

**Used in.** `dtDepth_neg`, together with `DecisionTree.negateLeaves_eval`: the
negated tree is a depth-preserving witness, giving `dtDepth (¬f) ≤ dtDepth f` and
(by symmetry of the argument) equality.
