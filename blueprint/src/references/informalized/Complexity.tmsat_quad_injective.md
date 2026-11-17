<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_quad_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the quadruple encoding

**Claim.** Equality of two nested quadruple encodings forces equality of their four components: $\alpha=\beta$, $x=y$, $n=m$, and $t=s$.

**Proof.** Apply injectivity of the pair encoding to the outermost equality. This identifies the first components, giving $\alpha=\beta$, and identifies the remaining nested encodings. Apply pair-encoding injectivity again to those remaining encodings to obtain $x=y$ and equality of the innermost encodings. A third application identifies the two unary words encoding $n,m$ and the two unary words encoding $t,s$. Equal lists have equal lengths, and the length of a word of $j$ ones is $j$; hence $n=m$ and $t=s$.

**Key facts.** `Turing.pairEncode_injective`.
