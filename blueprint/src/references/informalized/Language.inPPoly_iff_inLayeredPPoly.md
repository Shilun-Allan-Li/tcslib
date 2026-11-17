<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: Language.inPPoly_iff_inLayeredPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DAG and Layered Polynomial Size Equivalence

**Claim.** For every Boolean language, recognition by polynomial-size families of fan-in-two directed acyclic circuits is equivalent to recognition by polynomial-size layered circuit families using identity, NOT, and unbounded fan-in AND gates.

**Proof.** The forward implication applies the conversion theorem `Language.InPPoly.inLayeredPPoly`: a polynomial-size fan-in-two DAG family can be converted into a polynomial-size layered family using the specified gate operations, while preserving the recognized language. The reverse implication applies `Language.InLayeredPPoly.inPPoly`, which converts such a layered family into a polynomial-size fan-in-two DAG family recognizing the same language. Together these two conversions give the equivalence.

**Key facts.** `Language.InPPoly.inLayeredPPoly`, `Language.InLayeredPPoly.inPPoly`.
