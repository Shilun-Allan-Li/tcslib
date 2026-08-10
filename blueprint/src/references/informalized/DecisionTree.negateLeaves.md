<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: DecisionTree.negateLeaves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Negating the leaves of a decision tree

**Definition.** `DecisionTree.negateLeaves : DecisionTree n → DecisionTree n` is
defined by structural recursion:

- `.leaf b ↦ .leaf (!b)` — flip the output bit;
- `.branch v lo hi ↦ .branch v (negateLeaves lo) (negateLeaves hi)` — keep the
  queried variable `v` and the branching structure, recursing into both subtrees.

So the tree shape is untouched and only leaf labels change. The two `@[simp]`
consequences recorded immediately after it are `negateLeaves_eval`
(`T.negateLeaves.eval x = !(T.eval x)`, by induction with `split <;> simp_all` on
the branch case) and `negateLeaves_depth` (`T.negateLeaves.depth = T.depth`, by
induction on `DecisionTree.depth`).

**Used in.** `dtDepth_neg`, where it supplies the witness tree showing that
`dtDepth` is invariant under pointwise negation of the computed function — the
step that lets the CNF switching lemma be derived from the DNF one.
