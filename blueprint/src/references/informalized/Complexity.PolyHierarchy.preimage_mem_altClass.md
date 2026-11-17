<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Normalize.lean :: Complexity.PolyHierarchy.preimage_mem_altClass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preimages of alternating classes

**Claim.** The preimage under a polynomial-time computable function of a language in the level-$i$ alternating class with first quantifier $b$ belongs to that same class.

**Proof.** Write membership in the given alternating class using a language $V$ in polynomial time and a bound $C(|x|+1)^c$ on the quantified word length. The uniform-membership theorem says that, for any polynomial-time computable map and polynomial-time unary length function, the language described by applying the alternating predicate for $V$ to the map's output lies in the same alternating class (`Complexity.PolyHierarchy.mem_altClass_of_uniform`). Use the given map $f$ and the unary length function $y\mapsto C(|f(y)|+1)^c$, which is polynomial-time computable by `Complexity.PolyHierarchy.unaryPT_poly`. This yields a language whose defining condition at $y$ is the alternating predicate on $f(y)$. The original membership equivalence for $L$, applied to $f(y)$, identifies that condition with $f(y)\in L$, exactly the condition that $y$ belongs to the preimage.

**Key facts.** `Complexity.PolyHierarchy.mem_altClass_of_uniform`, `Complexity.PolyHierarchy.unaryPT_poly`.
