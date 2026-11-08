<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.query_iff_mem_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Query and Family Language Equivalence

**Claim.** For a fan-in-two circuit family $F$ and binary strings $y,e$, the pair encoding of $y,e$ belongs to the language accepted by $F$ exactly when the query using the encoding of the circuit of $F$ on inputs of that encoded length belongs to the circuit-value language.

**Proof.** Write $q=\langle y,e\rangle$. For the forward implication, a circuit-value witness consists of an input $x'$, a circuit $C'$, its fan-in-two property, the assertion that $C'$ evaluates to true on $x'$, and the equality expressing the queried encoding as $\langle C'.encode,x'\rangle$. Injectivity of pair encoding identifies $x'$ with $q$ and $C'.encode$ with the encoding of the circuit $F$ assigns to inputs of length $|q|$. Injectivity of circuit encoding then identifies $C'$ with that assigned circuit. The true evaluation therefore says precisely that $F$ accepts $q$, by the characterization of membership in the family language. Conversely, if $F$ accepts $q$, use $q$ itself as the input witness and the circuit assigned by $F$ to length $|q|$ as the circuit witness. The family hypothesis gives this circuit fan-in at most two; acceptance gives its evaluation on $q$ equal to true, and the required encoding equality holds by construction. Thus the circuit-value query holds.

**Key facts.** `Turing.pairEncode_injective`, `BoolCircuit.DAGCircuit.encode_injective`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
