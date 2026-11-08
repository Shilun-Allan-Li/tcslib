<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5IfLt_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Comparison Branch

**Claim.** If the unary encodings of $f$ and $g$, and the word functions $a$ and $b$, are polynomial-time computable, then the function returning $a(z)$ when $f(z)<g(z)$ and $b(z)$ otherwise is polynomial-time computable.

**Proof.** First compute the unary encoding of $f(z)+1$ in polynomial time by adding the constant unary word of length one to the unary encoding of $f(z)$ (`clA5Add_native`, using `clA5_pt_const`). Compare this value with $g(z)$ using the polynomial-time unary comparison construction (`clA5Le_native`), which returns the bit indicating whether $f(z)+1\le g(z)$. For natural numbers this condition is equivalent to $f(z)<g(z)$. The polynomial-time conditional construction (`clA5_pt_cond`) then selects $a(z)$ when that bit is true and $b(z)$ otherwise. The elementary equivalence between the comparison conditions identifies the resulting function with the one claimed.

**Key facts.** `Complexity.clA5Add_native`, `Complexity.clA5_pt_const`, `Complexity.clA5Le_native`, `Complexity.clA5_pt_cond`.
