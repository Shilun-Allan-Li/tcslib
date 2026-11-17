<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: Language.inSIZE_forty_two_pow_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Circuit Size Bound

**Claim.** Every Boolean language is recognized by a fan-in-two circuit family whose circuit on inputs of length $n$ has size at most $40\cdot 2^n/(n+1)$.

**Proof.** For each input length $n$, regard membership in the language as a Boolean function on $n$ bits. The existence theorem `BoolCircuit.exists_dagCircuit_faninTwo_size_le_div` supplies a fan-in-two DAG circuit computing that function with size at most $40\cdot2^n/(n+1)$. Choose one such circuit for each $n$ to form a family. Its size and fan-in conditions hold length by length. On a word $w$, the circuit at length $|w|$ outputs the membership bit of $w$, since the length-$|w|$ Boolean vector associated with $w$ is precisely the input used to evaluate that function. Hence the family recognizes exactly the given language.

**Key facts.** `BoolCircuit.exists_dagCircuit_faninTwo_size_le_div`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
