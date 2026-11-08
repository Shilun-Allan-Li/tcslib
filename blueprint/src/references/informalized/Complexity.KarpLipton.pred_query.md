<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.pred_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Circuit Queries

**Claim.** For polynomial-time computable functions $d,y,e$, the language of strings $z$ such that the nested pair encoding of $d(z)$ and the pair encoding of $y(z),e(z)$ belongs to circuit satisfiability is in $\mathsf{P}$.

**Proof.** First combine $y$ and $e$ into the map $z\mapsto\langle y(z),e(z)\rangle$, which is polynomial-time computable by closure under pair encoding. Pair this result with $d(z)$; the resulting nested encoding is again polynomial-time computable. By the polynomial-time preimage theorem, the inverse image of any language in $\mathsf{P}$ under a polynomial-time computable map belongs to $\mathsf{P}$. Apply this to the circuit satisfiability language, which is in $\mathsf{P}$, to obtain the claimed language.

**Key facts.** `BoolCircuit.CVAL_mem_P`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.preimage_mem_P`.
