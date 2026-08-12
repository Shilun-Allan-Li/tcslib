<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Circuit.toFeedForward_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Depth of the feedforward embedding of a circuit

**Claim.** For every `C : BoolCircuit.Circuit n`, `C.toFeedForward.depth = C.depth + 1`.

**Proof.** Immediate from `rfl`: the `depth` field of `Circuit.toFeedForward` is literally
written as `C.depth + 1`.

**Remark.** The extra layer is the input layer: layer `0` carries `Fin n`, one gate computes
`C.eval` from it, and layers `2, …, C.depth + 1` are identity wires. So the embedding costs
one layer, not a factor. (In `FeedForward`, `depth` counts gate layers, so the number of
node layers is `depth + 1` — hence `Fin (C.depth + 1 + 1)` appears as the layer index in
the surrounding proofs.)

**Used in.** Stated for the record and as the depth half of the tree-to-DAG cost accounting
alongside `Circuit.toFeedForward_size_le`.
