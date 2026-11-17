<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting-Time Comparison

**Claim.** If the cumulative miss probability for hitting $b$ from $a$ is bounded by $A$ at every horizon, then the cumulative miss probability for hitting $c$ from $a$ through step $N-1$ is at most $A$ plus that for hitting $c$ from $b$.

**Proof.** Suppose instead that the asserted inequality fails, and let $\varepsilon=\operatorname{hitTime}(c,N,a)-A-\operatorname{hitTime}(c,N,b)>0$. The comparison through an intermediate vertex gives, for every $M$, \[\operatorname{hitTime}(c,N,a)-\operatorname{hitTime}(c,N,b)\le \operatorname{hitTime}(b,M,a)+N\,\operatorname{missProb}(b,M,a).\] Using the assumed bound at horizon $M$, the definition of $\varepsilon$ therefore implies $\varepsilon\le N\,\operatorname{missProb}(b,M,a)$. Multiply by $M+1$. The estimate that $(M+1)$ times this miss probability is at most the hitting time through horizon $M+1$, together with the hypothesis at that horizon, yields $(M+1)\varepsilon\le NA$ for every $M$. Since $\varepsilon>0$, choose a natural number $M$ with $M>NA/\varepsilon$. Then $(M+1)\varepsilon>NA$, contradicting the bound just obtained. Thus the desired inequality holds.

**Key facts.** `Randomized.RegularMultigraph.hitTime_sub_le`, `Randomized.RegularMultigraph.succ_mul_missProb_le`.
