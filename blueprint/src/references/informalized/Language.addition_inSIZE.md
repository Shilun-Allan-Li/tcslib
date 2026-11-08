<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: Language.addition_inSIZE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-size circuits for addition

**Claim.** The language of Boolean-word encodings of addition is recognized by well-formed acyclic fan-in-two circuits whose size at input length $n$ is at most $6n+4$.

**Proof.** Use the adder circuit family. Its gates satisfy the well-formedness and fan-in-two requirements, its size at each input length $n$ is at most $6n+4$, and its recognized language is the addition language. These three properties give the required size-class witness.

**Key facts.** `BoolCircuit.adderFamily_hasFaninTwo`, `BoolCircuit.adderFamily_size_le`, `BoolCircuit.adderFamily_language`.
