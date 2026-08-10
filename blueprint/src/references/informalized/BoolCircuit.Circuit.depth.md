<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth of a general Boolean circuit

**Definition.** `Circuit.depth : Circuit n → Nat` is the length of the longest
root-to-leaf path, by structural recursion on the circuit tree:

- `Circuit.depth (.lit _) = 0` — a literal leaf has depth 0;
- `Circuit.depth (.node _ cs) = 1 + cs.foldr (fun c acc => max c.depth acc) 0` —
  a gate costs 1 plus the maximum depth of its children.

The gate flag `isAnd` is ignored: AND and OR nodes both count as one level.

**Remark.** The empty node `.node isAnd []` has depth `1`, not `0`, since the
`foldr` starts at `0` and the `1 +` is unconditional. The same `max`-fold is
also packaged separately as `Circuit.maxDepth`, but `Circuit.depth` inlines it,
which is why lemmas about children (`Circuit.depth1_children_are_lits`) have to
re-derive the fold bound by list induction.

**Used in.** Throughout the LMN layer-reduction development — the depth
hypotheses of `Circuit.exists_node_of_depth_ge_one`, `Circuit.depth0_is_lit`,
`Circuit.depth1_all_lits`, `Circuit.reidx_depth`, and the
`absorbOneLevel` / `exists_circuit_depth_reduction` family — as the quantity
being decreased.
