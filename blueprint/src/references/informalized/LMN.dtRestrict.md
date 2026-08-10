<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionMonotonicity.lean :: dtRestrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Applying a restriction to a decision tree

**Definition.** `dtRestrict : DecisionTree n → Restriction n → DecisionTree n`
pushes a partial assignment `ρ : Fin n → Option Bool` into a decision tree, by
structural recursion on the tree:

- `dtRestrict (.leaf b) ρ = .leaf b` — leaves are untouched;
- `dtRestrict (.branch var lo hi) ρ` inspects `ρ var`:
  - `some false` → `dtRestrict lo ρ` (the query is already answered `false`, so
    the node is deleted and only the `lo` subtree survives);
  - `some true` → `dtRestrict hi ρ`;
  - `none` → `.branch var (dtRestrict lo ρ) (dtRestrict hi ρ)` (the variable is
    still free, so the query is kept and both subtrees are restricted).

So every node querying a variable fixed by `ρ` is contracted to the subtree
selected by that value, and the remaining nodes are left in place. Nodes are
never added, which is what makes `dtRestrict_depth_le` hold; the branch
convention (`false → lo`, `true → hi`) matches `DecisionTree.eval`, which is
what makes `dtRestrict_eval` hold.

**Used in.** `dtRestrict_depth_le`, `dtRestrict_eval`, and through them
`dtDepth_restrictFn_le'` — the definition exists only to turn an optimal
decision tree for `f` into a witness tree for `restrictFn f ρ`.
