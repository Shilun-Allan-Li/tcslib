<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.gatesAcyclic_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity Under Concatenation

**Claim.** The concatenation of $gs$ and $hs$ is acyclic from index bound $n$ exactly when $gs$ is acyclic from $n$ and $hs$ is acyclic from $n+|gs|$.

**Proof.** Induct on the list $gs$, generalizing the starting bound $n$. If $gs$ is empty, the statement reduces directly to acyclicity of $hs$. If $gs$ begins with a gate, the characterization of acyclicity for a list with a leading gate separates the input bound for that gate from acyclicity of the remaining list with starting bound increased by one (gatesAcyclic_cons). Apply the induction hypothesis to the tail and reassociate the resulting index bounds; this gives precisely the bounds for the original concatenation and for the suffix beginning after all of $gs$.

**Key facts.** `BoolCircuit.gatesAcyclic_cons`.
