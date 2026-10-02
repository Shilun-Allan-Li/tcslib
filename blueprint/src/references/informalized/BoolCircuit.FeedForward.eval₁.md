<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: eval₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Evaluating a single-output feedforward circuit

**Definition.** For `F : FeedForward α inp out` with `[Unique out]` and an input assignment
`xs : inp → α`, `F.eval₁ xs : α` is `F.eval xs default` — the value of `F` at the unique
output node.

Unfolding `FeedForward.eval`, this is `F.evalNode (d := Fin.last F.depth) (F.nodes_last.symm.rec default) xs`: the output node is transported
back along the type equation `nodes_last` into the top node layer, and `evalNode` then
recurses down through the layers.

**Remark.** A one-line convenience wrapper around `FeedForward.eval`, which returns the
whole function `out → α`. The `Unique out` instance both guarantees there is exactly one
output node and provides the `default` used to name it, so no choice is involved.

**Used in.** `Circuit.toFeedForward_eval`, whose statement is about
`C.toFeedForward.eval₁ x` (there `out = Unit`).
