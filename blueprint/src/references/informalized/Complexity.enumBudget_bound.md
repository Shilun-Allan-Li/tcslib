<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumBudget_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound for Enumeration Budgets

**Claim.** For all natural numbers $a,C,c,d$, there exist natural numbers $A,e$ such that for every $n$, $a\,2^{C(n+1)^c}(n+C(n+1)^c+1)^d\le A\,2^{n^e}$.

**Proof.** Choose $k=\max(1,c)$ and $K=C+d(C+1)$. The polynomial factors in the exponent and base are controlled by $(n+1)^k$: both $(n+1)^c$ and $n+1$ are at most this quantity. Consequently, $n+C(n+1)^c+1\le(C+1)(n+1)^k$, and the exponent after absorbing the $d$th power into a power of two is at most $K(n+1)^k$. The elementary bound $m^d\le 2^{dm}$ for natural $m$ gives this absorption. Apply the exponential-growth bound (`Complexity.enumExponent_bound`) to $K,k$, obtaining constants $A_0,e$ with $2^{K(n+1)^k}\le A_0 2^{n^e}$. Multiplying by $a$ proves the claim with prefactor $aA_0$.

**Key facts.** `Complexity.enumExponent_bound`.
