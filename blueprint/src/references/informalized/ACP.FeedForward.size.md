<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Circuit size: the number of non-input nodes

**Definition.** For `F : FeedForward α inp out`,

`F.size = Nat.card (Σ d : Fin F.depth, F.nodes d.succ)`,

the cardinality of the sigma type collecting, for each gate layer index
`d : Fin F.depth`, the nodes of layer `d + 1`. Input nodes (layer `0`) are excluded, so
this counts exactly the gates. Marked `noncomputable` because `Nat.card` is.

**Remark.** `Nat.card` returns `0` on infinite types, so the definition is only
informative under a finiteness assumption such as `F.Finite`; `ACP.size_eq_sum_cards`
restates it as `∑ d : Fin F.depth, Fintype.card (F.nodes d.succ)` once every layer is a
`Fintype`.

**Used in.** `ACP.FeedForward.toCircuit_size_le`'s counterpart
`Circuit.toFeedForward_size_le`, `ACP.size_eq_sum_cards`,
`gateCountBefore_depth_eq_size`, and the size-form error bounds in
`RazborovSmolensky/CircuitSize.lean`.
