<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: DecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Decision trees on `n` Boolean variables

**Definition.** `DecisionTree n` is the inductive type with two constructors:

* `leaf (val : Bool) : DecisionTree n` — a leaf that outputs `val`;
* `branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n` — a query of variable
  `var`, continuing into `lo` when the variable reads `false` and into `hi` when it reads
  `true`.

Nothing constrains which variables may be queried: a variable may be queried more than
once along a path, or never, and the two subtrees of a branch are unrelated. The
accompanying `DecisionTree.eval` walks the tree (`if x i then hi.eval x else lo.eval x`)
and `DecisionTree.depth` is `0` on a leaf and `1 + max lo.depth hi.depth` on a branch, so
depth is the longest root-to-leaf path, not the shortest.

**Remark.** The type is not indexed by depth, and it carries no `DecidableEq`/`Repr`
derivation; every structural fact about it is proved by `induction T with | leaf | branch`.

**Used in.** `dtDepth`, `buildFullDTree`, `DecisionTree.deepPath`, and the switching-lemma
and LMN files.
