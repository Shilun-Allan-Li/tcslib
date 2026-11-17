<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFields_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Packing Preserves Concatenation

**Claim.** For any two finite lists of Boolean words $a$ and $b$, packing their concatenation gives the concatenation of their packed encodings.

**Proof.** Induct on the list $a$. If $a$ is empty, packing the concatenation leaves exactly the packed encoding of $b$. For the inductive step, write $a=w::as$. By the recursive definition of packing and the induction hypothesis, the packed encoding of $(w::as)++b$ is the pair encoding of $w$ with the concatenation of the packed encodings of $as$ and $b$. The pair encoding satisfies the associativity property that appending a suffix to its encoded tail is the same as encoding with that suffix appended to the tail (the pair-encoding append law, `Complexity.clPair_append`). Applying this law yields the pair encoding of $w$ with the packed encoding of $as++b$, which is precisely the packed encoding of $a$ followed by that of $b$.

**Key facts.** `Complexity.clPair_append`.
