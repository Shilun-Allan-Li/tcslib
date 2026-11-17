<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigma.lean :: Complexity.Meyer.query_mem_CVAL_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Query Membership Characterization

**Claim.** For a family of well-formed circuits with fan-in at most two, the encoding of its circuit for inputs of length $|q|$, paired with $q$, belongs to the language of satisfiable circuit encodings exactly when that circuit accepts $q$.

**Proof.** For the forward implication, membership in the satisfiable-circuit language supplies a witness input and a circuit, together with an accepting evaluation and an equality between their pair encoding and the encoding of the family circuit paired with $q$. Injectivity of pair encoding (`Turing.pairEncode_injective`) identifies the witness input with $q$ and identifies the two circuit encodings. Injectivity of circuit encoding (`DAGCircuit.encode_injective`) then identifies the circuits themselves. The supplied accepting evaluation is therefore an accepting evaluation of the family circuit on $q$; the family-language characterization (`DAGCircuitFamily.mem_language_iff`) gives membership in the family language. Conversely, if $q$ belongs to that language, choose $q$ and the family circuit at length $|q|$ as the witnesses for satisfiable-circuit membership. The fan-in hypothesis ensures that this circuit meets the required structural condition, and the language characterization gives its accepting evaluation. The required pair-encoding equality holds by construction.

**Key facts.** `Turing.pairEncode_injective`, `BoolCircuit.DAGCircuit.encode_injective`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
