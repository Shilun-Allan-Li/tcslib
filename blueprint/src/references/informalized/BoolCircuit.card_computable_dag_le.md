<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.card_computable_dag_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Functions Computed by Small DAG Circuits

**Claim.** The number of Boolean functions on $n$ variables computed by well-formed fan-in-two directed acyclic circuits of size at most $S$ is at most $(S+1)(3(S+1)^2)^S S$.

**Proof.** Encode each such circuit by a code whose decoding computes the same function. The circuit-encoding result ( `BoolCircuit.exists_code`) supplies such a code for every well-formed fan-in-two circuit of size at most $S$. Consequently, every function in the set being counted occurs among the functions obtained by evaluating all codes. The number of distinct functions in this image is at most the number of codes. Counting the possible codes gives $(S+1)(3(S+1)^2)^S S$, which proves the bound.

**Key facts.** `BoolCircuit.exists_code`.
