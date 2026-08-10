<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DecisionTree.length_deepPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The deep path has length equal to the tree depth

**Claim.** For every decision tree `T : DecisionTree n`,
`T.deepPath.length = T.depth`. That is, the root-to-leaf path extracted by
`DecisionTree.deepPath` — which at each `branch` descends into the deeper
subtree, ties going to `hi` — really is a deepest path, so it witnesses the
depth as a list of `(variable, direction)` pairs.

**Proof.** Structural `induction T`.

1. **`leaf _`.** Both sides are `0` by `rfl` (`deepPath = []`, `depth = 0`).
2. **`branch v lo hi`.** `simp only [deepPath]` exposes the `if hi.depth ≥ lo.depth`
   guard, and `split` handles the two branches.
   - Taken branch: the path is `(v, true) :: hi.deepPath`, so
     `simp only [List.length_cons, ih_hi, depth]` turns the goal into
     `hi.depth + 1 = 1 + max lo.depth hi.depth`, which `omega` closes using the
     branch condition `hi.depth ≥ lo.depth`.
   - Other branch: symmetric with `ih_lo` and `lo.depth > hi.depth`, again
     `omega`.

**Used in.** `TCSlib/BooleanAnalysis/Switching.lean` (four call sites), where a
depth bound on a decision tree is converted into a length bound on a concrete
restriction path.
