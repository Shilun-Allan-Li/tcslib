<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.lenLe_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time output-length comparison

**Claim.** For polynomial-time computable functions $f$ and $g$, the language of inputs on which $|g(z)|\le |f(z)|$ belongs to $\mathsf{P}$.

**Proof.** The polynomial-time preimage result for output-length comparison (`lenLe_preimage_mem_P`) applies to $f$ and $g$, giving that the language defined by $|g(z)|\le |f(z)|$ belongs to $\mathsf{P}$. The Boolean test in the statement accepts exactly when this inequality holds, so it defines that same language.

**Key facts.** `Complexity.lenLe_preimage_mem_P`.
