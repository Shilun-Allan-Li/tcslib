<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.four_mul_kb_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Growth of the Exponential Bound

**Claim.** For every finite nondeterministic Turing machine $N$ over the Boolean alphabet and all natural numbers $n,s$, the bound $k_b(N,n,s)$ satisfies $4k_b(N,n,s)\le k_b(N,n,s+1)$.

**Proof.** Write $c=\mathrm{codeK}(N)$. The exponent defining $k_b(N,n,s+1)$ is $c(s+1+\mathrm{lgv}(n)+1)=c(s+\mathrm{lgv}(n)+1)+c$, so the exponent law gives $k_b(N,n,s+1)=k_b(N,n,s)2^c$. The code-width bound (`two_le_codeK`) gives $c\ge2$, hence $4=2^2\le2^c$. Multiplying this inequality by $k_b(N,n,s)$ yields the claimed growth bound.

**Key facts.** `Complexity.LogProg.ExpBFS.two_le_codeK`.
