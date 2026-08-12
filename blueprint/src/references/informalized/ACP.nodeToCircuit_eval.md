<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: nodeToCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Tree-unrolling preserves the value of a node

**Claim.** Let `F : FeedForward Bool (Fin n) out` with AND/OR labelling `isAnd` and
per-gate fintypes `gfin`, and assume `hcorrect : F.IsAndOrGate isAnd gfin`, i.e. every
gate's `op.func` really is the `foldr`-AND (when `isAnd d v = true`) or `foldr`-OR (when
`false`) over its enumerated inputs. Then for every layer `m`, every node
`v : F.nodes ⟨m, hm⟩` and every assignment `x : Fin n → Bool`,
`(nodeToCircuit F isAnd gfin m hm v).eval x = F.evalNode v x`.

**Proof.** `induction m`.

* Base case: two `Nat.recAux`-unfoldings. `unfold nodeToCircuit; simp` gives
  `nodeToCircuit … 0 hm v = .lit ⟨F.nodes_zero ▸ v, true⟩`, and
  `unfold FeedForward.evalNode; simp` gives `F.evalNode v x = x (F.nodes_zero ▸ v)`.
  Rewriting by both and `simp [Circuit.eval, Lit.eval]` closes it, since a positive
  literal evaluates to the value of its variable.
* Step case: the same pair of unfoldings at `m + 1`, using `rw [Nat.recAux_succ]`, exposes
  the circuit as `.node (isAnd ⟨m, hm'⟩ v) (children)` and the node value as
  `(F.gates ⟨m, hm'⟩ v).op.func` applied to the layer-`m` values (`FeedForward.Gate.eval`,
  then `rfl`). The induction hypothesis, instantiated at each input wire
  `(F.gates ⟨m, hm'⟩ v).inputs i`, matches child subtrees with layer-`m` node values.
  Rewriting by `hcorrect ⟨m, hm'⟩ v` replaces `op.func` by the explicit fold, and
  `cases isAnd ⟨m, hm'⟩ v <;> simp [Circuit.eval, List.foldr_map, h_ih]` checks the AND and
  OR branches — `Circuit.eval` on a node is exactly the same `foldr`.

**Used in.** `ACP.FeedForward.toCircuit_eval`, by instantiating at the output layer.
