<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: evalNode_succ_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# One-step unfolding of `evalNode` at a successor layer

**Claim.** For a feedforward circuit `F : FeedForward α inp out`, a layer index
`d : Fin F.depth`, a node `u : F.nodes d.succ` of the next layer, and an input
`x : inp → α`, the value of `u` is the gate operation of `u` applied to the
values of `u`'s input nodes on layer `d.castSucc`:
`F.evalNode (d := d.succ) u x = (F.gates d u).op.func (fun i => F.evalNode (d := d.castSucc) ((F.gates d u).inputs i) x)`.

**Proof.** `rfl`. `FeedForward.evalNode` is defined by `Nat.recAux` on the
underlying layer number, whose successor branch is literally
`Gate.eval (F.gates ..) (ih ..)`, and `Gate.eval g xs = g.op.func (xs ∘ g.inputs)`;
so both sides are the same term up to unfolding.

**Remark.** A convenience rewrite only: it exists so downstream proofs can step
through a layer with `rw [evalNode_succ_eq]` instead of `show`/`dsimp` on the
recursor. Used in `stepLayerFamily` (the inductive layer step of the
Razborov–Smolensky degree argument) in the same file.
