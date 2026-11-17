<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.mem_uLen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership test for a unary-indexed length language

**Claim.** The encoding of $n$ unary ones paired with the bit expansion of $i$ belongs to the language determined by the lengths of $g$ exactly when $i$ is less than the length of $g(n)$.

**Proof.** The general unary-index membership lemma (mem_unaryIdx) identifies membership of the encoding of the unary string for $n$ paired with the bit expansion for $i$ with the defining predicate at $(n,i)$. Choosing that predicate to be $i<|g(n)|$ yields the result.

**Key facts.** `Complexity.mem_unaryIdx`.
