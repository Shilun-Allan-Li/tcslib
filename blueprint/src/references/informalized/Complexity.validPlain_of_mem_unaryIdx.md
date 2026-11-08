<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.validPlain_of_mem_unaryIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of unary-index encodings

**Claim.** If $y$ encodes a pair consisting of a length-$n$ all-ones string and the binary expansion of $i$, and a predicate $p(n,i)$ holds, then $y$ is a valid plain encoding.

**Proof.** Unpack the membership hypothesis to obtain $n$ and $i$ with $y$ equal to the specified pair encoding and with $p(n,i)$. Choose $n$ as the unary length and the binary expansion of $i$ as the second component of a valid plain encoding. The pair-encoding equation gives the required representation of $y$, and the binary expansion is canonical because its last bit is true whenever it is nonempty (`Complexity.LogProg.canon_bits`).

**Key facts.** `Complexity.LogProg.canon_bits`.
