<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.FinTM.configBound_logSpace_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration bound under logarithmic space

**Claim.** With $L(n)=\lfloor\log_2 n\rfloor+1$ and $B_M(n,s)=(|Q|+1)(n+2)3^{k(2s+1)}(2s+1)^k$, the configuration bound at space $cL(n)$ is at most $(|Q|+1)\,2\,2^{5kc+3k}(n+1)^{5kc+1}$.

**Proof.** Write $L=\lfloor\log_2 n\rfloor$ and $s=c(L+1)$. The standard logarithm estimate gives $2^L\le n+1$, also when $n=0$. Since $3\le 2^2$, we have $3^{k(2s+1)}\le 2^{2k(2s+1)}$. Also $2s+1\le 2^{s+1}$, so $(2s+1)^k\le 2^{k(s+1)}$. Combining these estimates, the product of the last two factors in $B_M$ is at most $2^{2k(2s+1)+k(s+1)}$. Substituting $s=c(L+1)$ and collecting exponents rewrites this power as $(2^L)^{5kc}2^{5kc+3k}$, which is at most $(n+1)^{5kc}2^{5kc+3k}$. Finally, $n+2\le 2(n+1)$. Multiplying by the state factor and regrouping gives $(|Q|+1)\,2\,2^{5kc+3k}(n+1)^{5kc+1}$, as claimed.
