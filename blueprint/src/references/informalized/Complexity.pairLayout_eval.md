<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.pairLayout_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the pair layout

**Claim.** For any natural numbers $n$ and $a$, and Boolean-valued functions $x$ on the first $n$ indices and $y$ on the first $a$ indices, evaluating the pair layout on their concatenated bit strings gives the self-delimiting encoding of those strings.

**Proof.** Let $z$ be the concatenation of the two finite bit strings obtained from $x$ and $y$. The finite-function concatenation identity identifies this with the list of values of `Fin.append x y`, so $z$ has length $n+a$. The range-indexed entries of $z$ in its first $n$ positions give precisely the list from $x$; those in the next $a$ positions give the list from $y$. Here the range-to-prefix fact (`range_map_getD`) identifies indexed entries, with the defaults harmless because the indices lie within the list. In the pair layout, each of the first $n$ input bits is repeated twice, then the two delimiter constants are emitted, and finally the next $a$ input bits are copied. Substituting the two identified lists into this construction yields exactly the self-delimiting encoding of the two strings.

**Key facts.** `Complexity.range_map_getD`.
