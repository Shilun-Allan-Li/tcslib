<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.noiseSensitivity_le_dimension_mul_delta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension Bound for Noise Sensitivity

**Claim.** For $0\le\delta\le1/2$, the noise sensitivity of a Boolean function on an $n$-dimensional cube is at most $n\delta$.

**Proof.** Apply the noise sensitivity bound by total influence (`noiseSensitivity_le_delta_mul_totalInfluence`), obtaining $\operatorname{NS}_\delta[f]\le\delta\,\mathcal I[f]$ with total influence in place of $\mathcal I[f]$. Boolean functions have total influence at most the dimension (`totalInfluence_toReal_mem_Icc`), and $\delta\ge0$, so this is at most $\delta n$. Commutativity of multiplication gives the stated form $n\delta$.

**Key facts.** `FABL.noiseSensitivity_le_delta_mul_totalInfluence`, `FABL.totalInfluence_toReal_mem_Icc`.
