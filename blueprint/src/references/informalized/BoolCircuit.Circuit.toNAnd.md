<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.toNAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Normalizing a circuit into AND-rooted normal form

**Definition.** `Circuit.toNAnd c : NAndCircuit n` rewrites an arbitrary
circuit as an alternating AND-rooted normal-form circuit, mutually recursively
with `Circuit.toNOr`:

- `.lit l ↦ .clause [l] (List.nodup_singleton _)` — a one-literal clause, whose
  `Nodup` side condition is the singleton instance.
- `.node true cs ↦ .node (cs.map Circuit.toNOr)` — an AND gate keeps its shape
  and each child is normalized OR-rooted, preserving alternation.
- `.node false cs ↦ .node [NOrCircuit.node (cs.map Circuit.toNAnd)]` — an OR
  gate at an AND position is wrapped in a one-child AND gate, since the result
  type forces an AND root.

**Remark.** The extra unary AND layer in the last case is the only source of
growth, and it is what makes the size bound `2 * c.size` rather than an
equality.

**Used in.** `toNAnd_toNOr_eval` / `toNAnd_eval` (semantics preserved),
`toNAnd_toNOr_litCount` / `toNAnd_litCount` (literal count preserved exactly),
and `toNAnd_toNOr_size_le` / `toNAnd_size_le` (`(c.toNAnd).size ≤ 2 * c.size`).
