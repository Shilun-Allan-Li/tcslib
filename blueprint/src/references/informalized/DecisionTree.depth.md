<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DecisionTree.depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth of a decision tree

**Definition.** `DecisionTree.depth : DecisionTree n → ℕ` is the maximum
root-to-leaf path length, by structural recursion:

- `DecisionTree.depth (.leaf _) = 0` — a leaf queries nothing;
- `DecisionTree.depth (.branch _ lo hi) = 1 + max lo.depth hi.depth` — a query
  costs one, then take the worse of the two subtrees.

Equivalently: the number of variables read on the worst-case input. The queried
variable index is irrelevant to the measure, so repeated queries of the same
variable still count.

**Remark.** The `1 +` is written on the left of the `max`, so goals about depth
usually finish with `omega` after `simp only [DecisionTree.depth]` rather than
by `max`-specific rewriting.

**Used in.** The quantity minimised by `dtDepth f =
Nat.find {d | ∃ T, T.depth ≤ d ∧ ∀ x, T.eval x = f x}`, bounded for the complete
tree by `buildFullDTree_depth`, and matched to the extracted deepest path by
`DecisionTree.length_deepPath` (`T.deepPath.length = T.depth`). It is the
complexity measure the switching lemma bounds.
