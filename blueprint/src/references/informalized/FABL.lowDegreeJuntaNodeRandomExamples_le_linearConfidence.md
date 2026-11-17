<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaNodeRandomExamples_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Node Random Example Bound

**Claim.** For every $n$, subset $P\subseteq[n]$, and natural numbers $k,b$, the node's random-example count at failure parameter $\delta_{k,b}$ is at most its stated linear-confidence coefficient times $(n+1)^{\lfloor3k/4\rfloor+3}(b+1)$.

**Proof.** Write $M$ for the restricted sample count and $B=(n+1)^{\lfloor3k/4\rfloor+3}$. The restricted-sample estimate bounds $M$ by its linear coefficient times $B(b+1)$ ( `lowDegreeJuntaRestrictedSampleCount_le_linearConfidence`). The restriction sampler bound says its count is at most $2^{k+1}M$ plus $16\cdot4^k$ times the Fourier estimator's failure bits ( `juntaRestrictionSampleCount_cast_le`); converting this rational estimate to natural numbers gives the same bound in the required type. For the half-failure parameter used by this sampler, the failure-bit estimate bounds those bits by $L_k(b+1)$ ( `lowDegreeJuntaHalfNodeFailureBits_le`). Since $B\ge1$, the remaining term $L_k(b+1)$ can also be bounded by $L_kB(b+1)$. Substituting the two bounds and collecting the coefficients gives exactly the node random-example coefficient times $B(b+1)$.

**Key facts.** `FABL.lowDegreeJuntaRestrictedSampleCount_le_linearConfidence`, `FABL.lowDegreeJuntaHalfNodeFailureBits_le`, `FABL.juntaRestrictionSampleCount_cast_le`.
