<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: evalNode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Value of a single node on a given input

**Definition.** For `F : FeedForward α inp out`, a layer index `d : Fin (F.depth + 1)`,
a node `node : F.nodes d` and an input assignment `xs : inp → α`, the value
`F.evalNode node xs : α` is defined by recursion on the numeral part of `d`
(`Nat.recAux`, after destructuring `d` as `⟨d, hd⟩`):

* **layer `0`:** transport the node along `F.nodes_zero : F.nodes 0 = inp` to get an
  input index, and return `xs` of it — `fun _ node' => xs (F.nodes_zero ▸ node')`;
* **layer `n + 1`:** take the gate attached to the node, `F.gates ⟨n, _⟩ node₀`, and
  evaluate it with `Gate.eval` against the recursively computed values of layer `n`
  (the recursor's `ih`). The bound `n < F.depth` needed to form the `Fin F.depth` index
  is `Nat.succ_lt_succ_iff.mp hd`.

The recursion is on `d` alone, with the proof `hd` and the node carried along as
arguments of the motive, so the returned function is applied to `hd` and `node` at the
end.

**Remark.** Because the layer-`0` case goes through the type-level transport
`F.nodes_zero ▸ _`, reasoning about `evalNode` proceeds by `unfold` plus
`Nat.recAux_zero` / `Nat.recAux_succ` rather than by `simp` on projections; both
`nodeToCircuit_eval` and `Circuit.toFeedForward_evalNode_const` do exactly this.

**Used in.** `ACP.FeedForward.eval` (and `eval₁`), `nodeToCircuit_eval`,
`Circuit.toFeedForward_evalNode_const`.
