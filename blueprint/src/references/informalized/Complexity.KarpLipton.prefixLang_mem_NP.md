<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.prefixLang_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Length Prefix Language in NP

**Claim.** For natural numbers $C,c$ and a language $V\in\mathsf{P}$, the prefix language whose witness makes the marker-removed second component followed by that witness have length $C(|x|+1)^c$, with $x$ the first component, belongs to $\mathsf{NP}$.

**Proof.** Apply the polynomially bounded prefix-language theorem with $\ell(y)=C(|\operatorname{fst}(y)|+1)^c$, where $\operatorname{fst}$ denotes the first component extracted by the decoder. The unary language for this length function is polynomial-time computable: the polynomial unary-construction result applies to the polynomial-time first-component decoder. For every input $y$, the decoder's first component has length at most $|y|$; consequently $C(|\operatorname{fst}(y)|+1)^c\le C(|y|+1)^c$. This supplies the required polynomial bound, so the prefix-language theorem yields membership in $\mathsf{NP}$.

**Key facts.** `Complexity.KarpLipton.prefixLangOf_mem_NP`, `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.polyTimeComputable_pairFstD`, `Complexity.length_pairFstD_le`.
