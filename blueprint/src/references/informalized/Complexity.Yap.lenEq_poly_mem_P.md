<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.lenEq_poly_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Equality Language

**Claim.** For polynomial-time computable functions $f,g$ and natural numbers $C,c$, the language of strings $z$ satisfying $|f(z)|=C(|g(z)|+1)^c$ belongs to $\mathsf P$.

**Proof.** The polynomial-time function theorem `unaryPT_poly` says that the map sending $z$ to a unary encoding of $C(|g(z)|+1)^c$ is polynomial-time computable. Apply the polynomial-time length-equality preimage result (`lenEq_preimage_mem_P`) to this function and to $f$. It gives a language in $\mathsf P$ where the two output lengths agree. A unary encoding has length equal to the natural number it encodes, so this equality is exactly $|f(z)|=C(|g(z)|+1)^c$.

**Key facts.** `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.lenEq_preimage_mem_P`.
