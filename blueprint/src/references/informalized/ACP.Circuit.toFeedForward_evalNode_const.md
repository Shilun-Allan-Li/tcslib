<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Circuit.toFeedForward_evalNode_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every non-input node of the embedding carries the circuit's value

**Claim.** Let `C : BoolCircuit.Circuit n` and `x : Fin n → Bool`. For every layer index
`m` with `0 < m` and `m < C.depth + 1 + 1`, and every node `v` of layer `m` in
`C.toFeedForward`, we have `C.toFeedForward.evalNode (d := ⟨m, hm⟩) v x = C.eval x`. The
positivity hypothesis is essential: layer `0` is the input layer, where `evalNode` returns
a single coordinate of `x`.

**Proof.** Induction on the layer index, after splitting off the excluded case.

* `rcases m with (_ | m) <;> simp_all +decide` discards `m = 0` (contradicts `hpos`) and
  leaves the goal at layer `m + 1`.
* `induction' m with m ih`.
* Base layer `1`: the gate is the layer-`0` gate `{ ι := Fin n, func := C.eval }`, so the
  two sides agree up to the type transport along `nodes_zero`; `congr! 1` closes it.
* Layer `m + 2`: the gate is `FeedForward.GateOp.id Bool`, so the node's value is the value
  of its single predecessor; `convert ih (Nat.lt_of_succ_lt hm) _ using 1` matches the goal
  against the induction hypothesis at layer `m + 1`.

**Remark.** Declared `private`, and its explanatory comment is a plain `/- … -/` block
rather than a `/-- … -/` docstring, so it does not appear in generated documentation.

**Used in.** `Circuit.toFeedForward_eval`, instantiated at `m := C.toFeedForward.depth`.
