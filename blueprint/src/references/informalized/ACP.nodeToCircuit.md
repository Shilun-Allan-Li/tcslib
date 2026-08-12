<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: nodeToCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tree-unrolling a feedforward node into a `BoolCircuit.Circuit`

**Definition.** `nodeToCircuit F isAnd gfin m hm v` turns a node `v` sitting on layer `m`
of a Boolean feedforward circuit `F : FeedForward Bool (Fin n) out` into a tree-shaped
`BoolCircuit.Circuit n`. It is defined by `Nat.recAux` on the layer index `m`:

* `m = 0` — the node is an input, so it becomes the positive literal
  `.lit ⟨F.nodes_zero ▸ v, true⟩` (the transport moves `v : F.nodes ⟨0, _⟩` to `Fin n`).
* `m + 1` — the node becomes `.node (isAnd ⟨m, _⟩ v) cs`, where `cs` is the list obtained
  by mapping the recursive call over `Finset.univ.val.toList` of the gate's input index
  type: one child subtree per input wire, namely the unrolling of
  `(F.gates ⟨m, _⟩ v).inputs i`.

The arguments `isAnd` picks the AND/OR label of each gate, and `gfin` supplies a `Fintype`
on each gate's input index type `(F.gates d v).op.ι` so that the wires can be enumerated.

**Remark.** Because `BoolCircuit.Circuit` is a tree (fanout ≤ 1) while a `FeedForward` is a
layered DAG, a node consumed by several downstream gates is *duplicated* once per consumer;
this is the source of the `(k + 1) ^ m` size blowup proved in `nodeToCircuit_size_le`.

**Status.** Declared `private noncomputable def`; it is the workhorse behind the public
`ACP.FeedForward.toCircuit`.
