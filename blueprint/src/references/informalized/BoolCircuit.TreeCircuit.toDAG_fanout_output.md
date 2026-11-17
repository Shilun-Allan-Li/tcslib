<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.TreeCircuit.toDAG_fanout_output -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output fanout

**Claim.** If the output vertex of the compiled DAG is at least $n$, then no gate reads that output vertex.

**Proof.** The fanout specification for the compiled DAG states that whenever the output index is at least $n$, its fanout is zero. Applying this condition gives the claimed conclusion.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_fanoutSpec`.
