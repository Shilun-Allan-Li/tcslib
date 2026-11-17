<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGTransform.lean :: BoolCircuit.DAGCircuit.rewrite_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Preserved by Rewriting

**Claim.** For every input assignment, rewriting the circuit preserves its output value.

**Proof.** Apply the invariant for the complete rewriting pass, `rewriteGates_inv`. Its value clause says that each old vertex has the same value as its mapped vertex in the rewritten gate list. The original output is a valid old vertex by the circuit's output bound, so this clause applies to it. The rewritten circuit designates precisely that mapped vertex as its output; hence the two output values agree.

**Key facts.** `BoolCircuit.rewriteGates_inv`.
