<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Le_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Comparison of Unary Values

**Claim.** If the unary encodings of $f(x)$ and $g(x)$ are polynomial-time computable, then the one-bit word indicating whether $f(x)\le g(x)$ is polynomial-time computable.

**Proof.** Use the polynomial-time operation that drops from one word as many symbols as the length of another (`clA5Drop_native`) on the two unary encodings. If their lengths are $f(x)$ and $g(x)$, the resulting word is empty exactly when $f(x)\le g(x)$. Testing whether this result equals the empty word is polynomial-time computable (`clA5_pt_eq`). The emptiness condition is therefore precisely the desired comparison bit.

**Key facts.** `Complexity.clA5Drop_native`, `Complexity.clA5_pt_eq`.
