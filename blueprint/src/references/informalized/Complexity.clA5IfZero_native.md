<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5IfZero_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Zero Branch

**Claim.** If the unary encoding of $f$ and the word functions $a,b$ are polynomial-time computable, then the function returning $a(z)$ when $f(z)=0$ and $b(z)$ otherwise is polynomial-time computable.

**Proof.** Test whether the unary encoding of $f(z)$ equals the empty word, using the polynomial-time word-equality test (`clA5_pt_eq`) with the empty word as the comparison value. A unary word is empty exactly when its encoded natural number is zero, so this test gives the desired branch condition. Applying the polynomial-time conditional construction (`clA5_pt_cond`) to that test and to $a,b$ yields the claimed function.

**Key facts.** `Complexity.clA5_pt_eq`, `Complexity.clA5_pt_cond`.
