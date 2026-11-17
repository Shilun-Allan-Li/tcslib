<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_flatten_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of equal-length concatenation

**Claim.** If every word in a finite list $L$ has length $w$, then their concatenation has length $w|L|$.

**Proof.** Induct on the list of words. The empty list has empty concatenation and length $0=w\cdot0$. For a list with first word $b$ and remaining list $L'$, the concatenation is $b$ followed by the concatenation of $L'$, so its length is $|b|+|L'|$. The hypothesis gives $|b|=w$, while the induction hypothesis gives $|L'|=w|L'|_{	ext{count}}$. Since the original list has one more element than $L'$, these lengths add to $w|L|$.
