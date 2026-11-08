<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: Language.exists_natToBits_mem_addition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Binary Addition

**Claim.** For any natural numbers $m,n$, some width $k$ makes the concatenation of their length-$k$ binary representations and the length-$k$ representation of $m+n$ a member of the addition language.

**Proof.** Choose $k=m+n+1$. This width is large enough to represent the sum: the standard bound $m+n<2^{m+n+1}$ follows from $r<2^r$ for positive $r$, together with monotonicity of powers of $2$. The fixed-width addition lemma states that whenever $m+n<2^k$, the three length-$k$ representations, concatenated in order, belong to the addition language (`Language.natToBits_mem_addition`). Applying it at the chosen width proves the claim.

**Key facts.** `Language.natToBits_mem_addition`.
