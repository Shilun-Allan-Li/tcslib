<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Certificate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Length Certificate Extension

**Claim.** If the assignment $a$ agrees with the binary word $x$ on its indexed positions, then its first $|x|+C(|x|+1)^e$ bits can be written as $x$ followed by a word $u$ of length $C(|x|+1)^e$.

**Proof.** Let $y$ be the finite word formed by reading $a$ at the indices from $0$ through $|x|+C(|x|+1)^e-1$. Its length is exactly that bound. Agreement of $a$ with $x$ on indices below $|x|$, together with the fact that reading this finite word returns the assigned bit at each in-range index (`Complexity.clA5ReadInput_get`), shows that the prefix of $y$ of length $|x|$ is $x$. Take $u$ to be the suffix obtained by dropping those first $|x|$ bits. Its length is the remaining $C(|x|+1)^e$, and the list decomposition into prefix and suffix gives $y=x++u$.

**Key facts.** `Complexity.clA5ReadInput_get`.
