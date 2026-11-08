<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.TreeCircuit.toDAG_fanout_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout bound for compiled circuits

**Claim.** Every vertex $v\ge n$ in the compiled DAG is read by at most one gate.

**Proof.** The compiled circuit's fanout specification includes the bound that every index at least $n$ has fanout at most one. Applying that bound to $v$ gives the result.

**Key facts.** `BoolCircuit.TreeCircuit.toDAG_fanoutSpec`.
