<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjWalk.descr_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Description of Unary Inputs

**Claim.** For every circuit family $C$ and natural number $n$, the description assigned to the unary input of $n$ ones is the encoding of the circuit for inputs of length $n$.

**Proof.** The definition of the description selects the circuit according to the length of its input. The list of $n$ ones has length $n$, so this selection chooses $C_n$; substituting that length into the definition gives exactly the encoding of $C_n$.
