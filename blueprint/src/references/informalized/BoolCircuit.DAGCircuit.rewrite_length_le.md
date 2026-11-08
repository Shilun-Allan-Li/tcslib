<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.DAGCircuit.rewrite_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Count Bound After Rewriting

**Claim.** The rewritten circuit has at most the sum, over the original gates, of each gate's number of inputs plus two gates.

**Proof.** The invariant for the complete rewriting pass, `rewriteGates_inv`, includes a length bound: the rewritten gate list has length at most the sum over the original list of each gate's input count plus two. The rewritten circuit uses exactly this list as its gates, so the invariant gives the claimed bound directly.

**Key facts.** `BoolCircuit.rewriteGates_inv`.
