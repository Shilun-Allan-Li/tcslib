<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.lenLe_poly_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length-Bound Language

**Claim.** For polynomial-time computable functions $f,g$ and natural numbers $C,c$, the language of strings $z$ satisfying $|f(z)|\le C(|g(z)|+1)^c$ belongs to $\mathsf P$.

**Proof.** The unary polynomial-time function theorem `unaryPT_poly` provides a polynomial-time computable unary output whose length is $C(|g(z)|+1)^c$. Apply the polynomial-time length-inequality preimage result (`lenLe_preimage_mem_P`) with this unary function as the upper-bound side and $f$ as the other function. It yields a language in $\mathsf P$ defined by the inequality between their output lengths. Since the unary output length is the specified bound, that language is exactly the one claimed.

**Key facts.** `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.lenLe_preimage_mem_P`.
