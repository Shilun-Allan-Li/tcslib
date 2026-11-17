<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.mem_uBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership test for a unary-indexed bit language

**Claim.** The encoding of $n$ unary ones paired with the bit expansion of $i$ belongs to the language determined by $g$ exactly when the bit of $g(n)$ at position $i$ is $1$.

**Proof.** The general unary-index membership lemma (mem_unaryIdx) says that the encoding of the unary string for $n$ paired with the bit expansion for $i$ belongs to the language defined by any predicate $p(n,i)$ exactly when that predicate holds. Taking $p(n,i)$ to mean that the $i$th bit of $g(n)$ is $1$ gives the stated equivalence.

**Key facts.** `Complexity.mem_unaryIdx`.
