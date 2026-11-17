<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.DAGCircuit.rewrite_new_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Property of Rewritten Gates

**Claim.** Every gate in the rewritten circuit satisfies the property $P$.

**Proof.** The invariant for the complete rewriting pass, `rewriteGates_inv`, asserts that every gate in the resulting gate list satisfies $P$. The rewritten circuit takes that list as its gates, so the asserted property applies to every gate of the rewritten circuit.

**Key facts.** `BoolCircuit.rewriteGates_inv`.
