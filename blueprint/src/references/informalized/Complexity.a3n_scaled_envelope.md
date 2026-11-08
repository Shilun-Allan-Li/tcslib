<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_scaled_envelope -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Envelope for a Scaled Expression

**Claim.** For all natural numbers $C,c,K,r,s$, there are natural numbers $A,e$ such that for every $n$, $K(n+C(2^{s(n+1)})^c+1)^r\le A(2^n)^e$.

**Proof.** Set $q=(s^c+1)(n+1)^{c+1}$. The proof bounds $(s(n+1))^c$ and $n+1$ by $q$. Since $n+1<2^{n+1}$ and $n+1\le q$, it follows that $n+1\le 2^q$. The first bound also gives $C2^{(s(n+1))^c}\le C2^q$, hence $n+C2^{(s(n+1))^c}+1\le (C+1)2^q$. Raising this inequality to the power $r$ and multiplying by $K$ bounds the target by $K(C+1)^r2^{rq}$. Apply the exponential domination result (`Complexity.a2_exponent_bound`) with parameters $r(s^c+1)$ and $c+1$: it supplies constants $A,e$ for which $2^{r(s^c+1)(n+1)^{c+1}}\le A(2^n)^e$. Since $rq=r(s^c+1)(n+1)^{c+1}$, absorbing the fixed factor $K(C+1)^r$ into the coefficient yields the required $A,e$.

**Key facts.** `Complexity.a2_exponent_bound`.
