<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.pred_len_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Equality Language

**Claim.** For natural numbers $C,c$ and a polynomial-time computable function $f$, the language of strings $z$ satisfying $|f(z)|=C\,(|g(z)|+1)^c$, where $g$ is the iterated first projection with the empty-string fallback, belongs to $\mathsf{P}$.

**Proof.** By polynomial-time computability of the iterated first projection and the unary polynomial construction (`unaryPT_poly`), the function whose output length is $C\,(|g(z)|+1)^c$ is polynomial-time computable. The given function $f$ is also polynomial-time computable. The length-equality preimage theorem (`lenEq_preimage_mem_P`) therefore puts the language where these two output lengths agree in $\mathsf{P}$. Its defining equality is precisely $|f(z)|=C\,(|g(z)|+1)^c$, as required.

**Key facts.** `Complexity.KarpLipton.polyTimeComputable_gx`, `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.lenEq_preimage_mem_P`.
