<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuit.depthAt_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of an Input

**Claim.** Every input vertex $i<n$ has depth zero.

**Proof.** The depth list is formed by starting with $n$ zeros and then appending the gate depths. At any position $i<n$, its entry is therefore unchanged from the initial list (`runWith_getD_of_lt`); the initial list has value zero there. By definition, the depth at that vertex is this entry, so it is zero.

**Key facts.** `BoolCircuit.runWith_getD_of_lt`.
