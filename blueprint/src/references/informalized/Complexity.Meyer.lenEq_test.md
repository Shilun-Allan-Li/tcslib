<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.lenEq_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time output-length equality

**Claim.** For polynomial-time computable functions $f$ and $g$, the language of inputs on which their outputs have equal length belongs to $\mathsf{P}$.

**Proof.** The polynomial-time preimage result for output-length equality (`lenEq_preimage_mem_P`) applies directly to $f$ and $g$, using their assumed polynomial-time computability. It puts the language defined by $|f(z)|=|g(z)|$ in $\mathsf{P}$. The theorem's language uses the Boolean test that this equality holds; that test is true exactly when the equality holds, so it defines the same language.

**Key facts.** `Complexity.lenEq_preimage_mem_P`.
