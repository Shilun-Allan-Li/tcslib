<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Constant Circuit

**Claim.** For every number of input bits, Boolean value, and input assignment, the circuit consisting of the single constant gate evaluates to that Boolean value.

**Proof.** The constant circuit has one gate with no inputs and output vertex $n$. Running that gate appends its value to the list of input values (`BoolCircuit.runWith_cons`). An AND gate with no inputs evaluates to true, while an OR gate with no inputs evaluates to false; the constant gate chooses the former exactly when the desired value is true. Thus the list entry at vertex $n$ is precisely the chosen Boolean value, which is the circuit evaluation.

**Key facts.** `BoolCircuit.runWith_cons`.
