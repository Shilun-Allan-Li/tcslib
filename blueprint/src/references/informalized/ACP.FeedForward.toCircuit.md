<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: toCircuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tree-unrolling a feedforward AND/OR circuit

**Definition.** Let `F : FeedForward Bool (Fin n) out`, let
`isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool` label each gate as AND or OR, let
`gfin` give a `Fintype` on each gate's input index type, and let `o : out`. Then

`F.toCircuit isAnd gfin o = nodeToCircuit F isAnd gfin F.depth (Fin.last F.depth).isLt (F.nodes_last.symm.rec o)`,

a `BoolCircuit.Circuit n`. It is the private recursion `nodeToCircuit` started at the
output node named by `o`, transported into the last layer along `F.nodes_last`.
`noncomputable`, inheriting that from `nodeToCircuit`.

The recursion `nodeToCircuit` itself expands a node of layer `m` as: a layer-`0` node
becomes the positive literal `.lit ⟨F.nodes_zero ▸ v, true⟩`; a node of layer `m + 1`
becomes `.node (isAnd _ v)` with one recursively expanded child per input wire,
enumerated by `Finset.univ.val.toList.map`.

**Remark.** A `BoolCircuit.Circuit` is tree-shaped (fan-out ≤ 1) while a `FeedForward`
is a layered DAG, so a node read by `k` downstream gates is duplicated `k` times — the
size cost of this, `(k + 1) ^ F.depth`, is `ACP.FeedForward.toCircuit_size_le`.

**Used in.** `ACP.FeedForward.toCircuit_eval`, `ACP.FeedForward.toCircuit_size_le`.
