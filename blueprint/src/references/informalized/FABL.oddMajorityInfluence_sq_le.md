<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluence_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd majority influence bound

**Claim.** For every $m\ge 0$, the squared odd-majority influence satisfies $I_m^2\le \dfrac{2((2m+1)+1)}{\pi(2m+1)^2}$.

**Proof.** Set $N=2m+1$, which is positive. Wallis's inequality gives $\frac{N}{N+1}\frac{\pi}{2}\le W_m$, where $W_m$ is the $m$th Wallis factor. Multiplying by the positive quantity $2(N+1)$ yields $N\pi\le 2(N+1)W_m$. The identity relating the squared influence to the Wallis factor, $I_m^2 N W_m=1$ (`oddMajorityInfluence_sq_mul_wallis`), then rewrites the desired left side as $1/(NW_m)$. Since $NW_m>0$ and $\pi N^2>0$, cross-multiplication reduces the claimed bound to $N(N\pi)\le N\bigl(2(N+1)W_m\bigr)$, which follows from the inequality just obtained and $N>0$.

**Key facts.** `FABL.oddMajorityInfluence_sq_mul_wallis`.
