<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean :: Complexity.LogProg.SavitchARM.radius_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Radius Bound

**Claim.** If $k+c+1\le E$, then $c(n^k+1)\le(n+2)^E$ for all natural numbers $n,k,c,E$.

**Proof.** First, $n^k\le(n+2)^k$ and $1\le(n+2)^k$, so $n^k+1\le2(n+2)^k$. Also $c<2^c\le(n+2)^c$, hence $2c\le2(n+2)^c$. Multiplying the first bound by $c$ and then applying the second gives $c(n^k+1)\le2(n+2)^{k+c}$. Since $n+2\ge2$, this is at most $(n+2)^{k+c+1}$, which is at most $(n+2)^E$ by the assumed exponent inequality.
