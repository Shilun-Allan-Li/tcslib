<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.PPoly_eq_LayeredPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Polynomial-Size Circuit Classes

**Claim.** The class of languages computable by polynomial-size families of fan-in-two DAG circuits equals the class computable by polynomial-size finite-layer circuit families using the specified standard gate operations.

**Proof.** Fix a language $L$. Its membership in the polynomial-size DAG circuit class is equivalent to its membership in the polynomial-size layered circuit class (`Language.inPPoly_iff_inLayeredPPoly`). Thus the two classes contain exactly the same languages, and are equal.

**Key facts.** `Language.inPPoly_iff_inLayeredPPoly`.
