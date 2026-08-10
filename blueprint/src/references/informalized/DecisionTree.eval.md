<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DecisionTree.eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating a decision tree

**Definition.** `DecisionTree.eval : DecisionTree n → (Fin n → Bool) → Bool`
runs an input `x` down the tree by structural recursion:

- `DecisionTree.eval (.leaf b) _ = b` — a leaf returns its stored bit,
  independently of the input;
- `DecisionTree.eval (.branch i lo hi) x = if x i then hi.eval x else lo.eval x`
  — query variable `i` and recurse into `hi` when the bit is `true`, `lo` when
  it is `false`.

This fixes the orientation of the two subtrees of `DecisionTree.branch`
(`hi` = true-branch, `lo` = false-branch), which the rest of the development
relies on.

**Remark.** The function is total and computes on all of `Fin n → Bool`; a tree
of depth `d` reads at most `d` coordinates of `x`, but that is a separate fact
proved where it is needed rather than visible in the definition.

**Used in.** The predicate "`T` computes `f`", i.e. `∀ x, T.eval x = f x`, which
is the second component of the set `Nat.find`s over in `dtDepth`; established for
the complete tree by `buildFullDTree_eval`. It is also the semantics side of the
canonical-tree and restriction work (`Switching/CanonicalDTree.lean`,
`Switching/Restriction.lean`) and of the Fourier-side files
`LMN/DecisionTreeFourier.lean` and `LMN/RestrictionFourier.lean`.
