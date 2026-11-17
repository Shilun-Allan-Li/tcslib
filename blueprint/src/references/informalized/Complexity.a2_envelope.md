<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_envelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential-Time Envelope

**Claim.** For all natural numbers $C,c,K,r$, there are natural numbers $A,e$ such that $K(n+C\cdot2^{(n+1)^c}+1)^r\le A\cdot2^{n^e}$ for every natural number $n$.

**Proof.** Apply the exponential domination estimate (a2_exponent_bound) with exponents $r$ and $c+1$, obtaining $A_0,e$ such that $2^{r(n+1)^{c+1}}\le A_0 2^{n^e}$. Since $(n+1)^c\le(n+1)^{c+1}$ and $n+1\le(n+1)^{c+1}$, while $n+1<2^{n+1}$, we have $n+1\le2^{(n+1)^{c+1}}$. These bounds yield $n+C2^{(n+1)^c}+1\le(C+1)2^{(n+1)^{c+1}}$. Raise this inequality to the power $r$, multiply by $K$, and use the estimate from a2_exponent_bound. The resulting bound has coefficient $A=K(C+1)^rA_0$ and exponent $e$, as required.

**Key facts.** `Complexity.a2_exponent_bound`.
