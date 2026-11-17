<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.b2f_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Boolean encoding

**Claim.** The encoding of Booleans in $\mathrm{Fin}(2)$ is injective: if two Booleans have the same encoding, then they are equal.

**Proof.** The encoding is the inverse of the equivalence between Booleans and $\mathrm{Fin}(2)$. Every equivalence is injective, so equality of the encoded values implies equality of the original Booleans.
