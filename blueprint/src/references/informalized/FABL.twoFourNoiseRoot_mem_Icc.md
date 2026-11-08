<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.twoFourNoiseRoot_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise parameter lies in the unit interval

**Claim.** The number $\sqrt{1/3}$ lies in the interval $[-1,1]$.

**Proof.** The lower bound follows from the nonnegativity of the noise root (`FABL.twoFourNoiseRoot_nonneg`), which in particular makes it at least $-1$. For the upper bound, the square root is at most $1$ because its radicand $1/3$ is at most $1$. Together these inequalities place the root in $[-1,1]$.

**Key facts.** `FABL.twoFourNoiseRoot_nonneg`.
