<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.toNOr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Normalizing a circuit into OR-rooted normal form

**Definition.** `Circuit.toNOr c : NOrCircuit n` is the dual of
`Circuit.toNAnd`, defined in the same `mutual` block:

- `.lit l ↦ .clause [l] (List.nodup_singleton _)` — a one-literal clause.
- `.node false cs ↦ .node (cs.map Circuit.toNAnd)` — an OR gate keeps its
  shape, its children normalized AND-rooted.
- `.node true cs ↦ .node [NAndCircuit.node (cs.map Circuit.toNOr)]` — an AND
  gate at an OR position gets a unary OR wrapper so the root matches the
  result type.

**Remark.** Exchanging `true`/`false` and `NAnd`/`NOr` turns this definition
into `Circuit.toNAnd` verbatim; the two are genuinely mutual because each gate
type dispatches to the other on its children.

**Used in.** `toNOr_eval`, `toNOr_litCount`, and `toNOr_size_le`, each obtained
as the second component of the combined statements `toNAnd_toNOr_eval`,
`toNAnd_toNOr_litCount`, `toNAnd_toNOr_size_le` — proved simultaneously
because the mutual recursion makes neither half provable alone.
