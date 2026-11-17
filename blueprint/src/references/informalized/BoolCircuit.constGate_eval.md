<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.constGate_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a constant gate

**Claim.** For every Boolean value $b$ and every list of Boolean values, the gate representing $b$ evaluates to $b$, independently of the list.

**Proof.** Consider the two cases for $b$. When $b$ is true, the gate is AND with no arguments, whose empty conjunction is true. When $b$ is false, it is OR with no arguments, whose empty disjunction is false. Thus the evaluation equals $b$ in both cases, whatever values the list contains.
