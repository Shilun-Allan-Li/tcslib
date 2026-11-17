<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.poly_add_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial input bound

**Claim.** For natural numbers $a,k,n,s$, if $s\le a(n+1)^k$, then $n+s\le (a+1)(n+1)^{k+1}$.

**Proof.** Since $n+1\ge1$, we have $n+1\le(n+1)^{k+1}$. Also, because $k\le k+1$ and the base is at least one, $(n+1)^k\le(n+1)^{k+1}$. Multiplying the latter inequality by $a$ and using the hypothesis gives $s\le a(n+1)^{k+1}$. Adding the bounds for $n$ and $s$ yields $n+s\le(n+1)^{k+1}+a(n+1)^{k+1}=(a+1)(n+1)^{k+1}$.
