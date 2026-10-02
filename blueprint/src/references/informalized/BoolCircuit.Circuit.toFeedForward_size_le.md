<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Circuit.toFeedForward_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Size of the feedforward embedding of a circuit

**Claim.** For every `C : BoolCircuit.Circuit n`,
`C.toFeedForward.size ≤ C.size * (C.depth + 1)`, where `FeedForward.size` is
`Nat.card (Σ d : Fin depth, nodes d.succ)`.

**Proof.** The bound is slack: the embedding has exactly `C.depth + 1` non-input nodes (one
per layer), and `C.size ≥ 1`.

* `refine' le_trans _ (Nat.le_mul_of_pos_left _ <| BoolCircuit.Circuit.one_le_size C)`
  reduces the goal to `C.toFeedForward.size ≤ C.depth + 1`, using
  `Circuit.one_le_size` for the positive factor.
* `unfold FeedForward.size`, then rewrite the `nodes` field to its defining branch
  `fun d => if d.val = 0 then Fin n else Unit` (`funext`, `cases x`, `rfl`).
* Every index of the form `d.succ` has nonzero value, so the branch always takes `Unit`;
  `simp +decide` collapses the sigma type's cardinality to the number of layers.
* `exact Nat.le_refl C.toFeedForward.depth` finishes.

**Remark.** The explanatory comment above the theorem is a plain `/- … -/` block, not a
docstring. As it notes, the true size is `C.depth + 1`; the product form is stated because
it is the shape the tree/DAG cost comparison in this file uses.
