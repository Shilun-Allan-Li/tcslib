<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.eventually_poly_sq_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial square is eventually exponential-bounded

**Claim.** For natural numbers $k$ and $A$, there is an $N$ such that every $n\ge N$ satisfies $A(n^k+1+n+1)^2\le 2^n$.

**Proof.** Apply the eventual polynomial bound with coefficient $9A$ and exponent $2k+2$, obtaining an $N$ for which $9A(n+1)^{2k+2}\le 2^n$ whenever $n\ge N$ (`eventually_poly_le_two_pow`). For every $n$, monotonicity of natural-number powers gives $n^k\le(n+1)^{k+1}$ and $n+1\le(n+1)^{k+1}$. Consequently $n^k+1+n+1\le 3(n+1)^{k+1}$. Squaring and using the power laws yields $(n^k+1+n+1)^2\le 9(n+1)^{2k+2}$. Multiplying by $A$ and applying the chosen eventual bound proves the claim.

**Key facts.** `Complexity.eventually_poly_le_two_pow`.
