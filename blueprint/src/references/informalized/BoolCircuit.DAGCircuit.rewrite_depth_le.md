<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.DAGCircuit.rewrite_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bound for circuit rewriting

**Claim.** If every gate of $C$ satisfies the rewriting condition, and each replacement gadget has output depth at most $c$ plus the maximum depth of its inputs, then the rewritten circuit has depth at most $c$ times the depth of $C$.

**Proof.** The rewriting invariant theorem (`rewriteGates_inv`) supplies, for every original vertex, a corresponding vertex in the rewritten circuit whose depth is at most $c$ times the original vertex's depth. The rewritten circuit's output is the corresponding vertex for $C$'s output. Applying the invariant at that output vertex and using the definition of circuit depth gives the claimed bound.

**Key facts.** `BoolCircuit.rewriteGates_inv`.
