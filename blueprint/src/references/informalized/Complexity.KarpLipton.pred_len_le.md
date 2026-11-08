<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.KarpLipton.pred_len_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Length Bound Language

**Claim.** For natural numbers $C,c$ and a polynomial-time computable function $f$, the language of strings $z$ satisfying $|f(z)|\le C\,(|g(z)|+1)^c$, where $g$ is the iterated first projection with the empty-string fallback, belongs to $\mathsf{P}$.

**Proof.** The iterated first projection is polynomial-time computable, so `unaryPT_poly` makes the function whose output length is $C\,(|g(z)|+1)^c$ polynomial-time computable. Apply the length-inequality preimage theorem (`lenLe_preimage_mem_P`) with this bound-producing function in the theorem's first function position and the given $f$ in its second. The resulting condition compares the bound's output length, $C\,(|g(z)|+1)^c$, with $|f(z)|$ in the direction that yields the stated inequality. Thus the language belongs to $\mathsf{P}$.

**Key facts.** `Complexity.KarpLipton.polyTimeComputable_gx`, `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.lenLe_preimage_mem_P`.
