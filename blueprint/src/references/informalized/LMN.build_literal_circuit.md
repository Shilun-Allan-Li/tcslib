<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: build_literal_circuit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A signed fan-in-k gate is a depth-≤-1 circuit

**Claim.** For a gate type `isAnd : Bool`, an arity `k : ℕ` and signs
`signs : Fin k → Bool`, there is a circuit `c' : Circuit k` with `c'.depth ≤ 1` that
evaluates, on every `g : Fin k → Bool`, exactly like the node
`Circuit.node isAnd ((List.finRange k).map (fun j => Circuit.lit ⟨j, signs j⟩))`.

**Proof.** A packaging lemma: the witness is literally that node, so the evaluation
clause is `rfl` and the only content is the depth bound.

1. `exact ⟨Circuit.node isAnd ((List.finRange k).map …), _, fun g => rfl⟩`.
2. Depth: `Circuit.depth` of a node is `1 + foldr max 0` over the children, and every
   child is a `Circuit.lit` of depth `0`. Proved by `induction' k` — `k = 0` gives the
   empty node (`cases isAnd <;> simp [Circuit.depth]`), and the successor case by an
   induction over `List.finRange (k+1)` with `simp_all +arith [Circuit.depth]`.

**Used in.** `exists_circuit_depth_reduction_depth2`, to build the new top gate over the
per-child DNF gates once each depth-≤-1 child has been replaced by a signed literal.
