<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: FeedForward.IsAndOrGate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every gate is an AND or an OR

**Definition.** Let `F : FeedForward Bool (Fin n) out`, let
`isAnd : ∀ d : Fin F.depth, F.nodes d.succ → Bool` label each non-input node, and let
`gfin` supply a `Fintype` instance for the input-index type of each gate.
`F.IsAndOrGate isAnd gfin` asserts that for every layer `d`, every node `v` of layer
`d + 1`, and every input tuple `xs : (F.gates d v).op.ι → Bool`, the gate's function agrees
with the labelled connective:

* if `isAnd d v` is `true`, `(F.gates d v).op.func xs` equals
  `Finset.univ.val.toList.foldr (fun i acc => xs i && acc) true`;
* if it is `false`, it equals `Finset.univ.val.toList.foldr (fun i acc => xs i || acc)
  false`.

The fold is over `Finset.univ.val.toList` for the supplied `Fintype`, so the conjunction /
disjunction is taken in that enumeration order, seeded with `true` / `false`.

**Remark.** This is the gate restriction under which a `FeedForward Bool` circuit can be
tree-unrolled into a `BoolCircuit.Circuit`: the same `foldr` shape appears in
`Circuit.eval`, which is why `nodeToCircuit_eval` can close its cases with
`simp [Circuit.eval, List.foldr_map, h_ih]`. The `Fintype` data is a parameter rather than
an instance, so the predicate depends on the chosen enumeration; nothing here asserts the
gates have bounded fanin (that is a separate hypothesis `hk` in the size lemmas).

**Used in.** `nodeToCircuit_eval` and `FeedForward.toCircuit_eval`.
