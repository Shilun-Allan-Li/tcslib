<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.encode_mem_dagCktSatLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Satisfiable Circuit Language

**Claim.** For a natural number $n$ and a directed acyclic circuit $C$ on $n$ inputs, its encoding belongs to the language of encodings of fan-in-two satisfiable circuits if and only if $C$ is fan-in-two and satisfiable.

**Proof.** Membership in the language is equivalent to the existence of a decoded circuit pair whose decoding is the given word and whose circuit satisfies the required fan-in and satisfiability conditions (BoolCircuit.mem_dagCktSatLang_iff_decode). For the word encoding $C$, the decoding theorem identifies the decoded pair as $(n,C)$ (BoolCircuit.DAGCircuit.decode_encode). Substituting this pair into the membership criterion leaves exactly the assertion that $C$ is fan-in-two and satisfiable.

**Key facts.** `BoolCircuit.mem_dagCktSatLang_iff_decode`, `BoolCircuit.DAGCircuit.decode_encode`.
