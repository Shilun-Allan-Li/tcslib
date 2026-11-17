<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.gatesAcyclic_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of the empty list

**Claim.** For every $n$, the empty gate list is acyclic from $n$ if and only if true.

**Proof.** The empty list is acyclic from every bound because it has no gate positions to check (\texttt{GatesAcyclic.nil}). Therefore its acyclicity is equivalent to the proposition true.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`.
