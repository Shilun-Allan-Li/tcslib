<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalInverse_mem_Ioc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Inverse Half-Interval Bound

**Claim.** For every positive natural number $w$, $2^{-w}\in(0,1/2]$.

**Proof.** The inverse of $2^w$ is positive because $2^w>0$. Since $w\ge1$ and $2\ge1$, monotonicity of natural powers gives $2\le2^w$. Taking reciprocals of these positive quantities reverses the inequality, so $(2^w)^{-1}\le1/2$. Together these inequalities place the critical inverse in $(0,1/2]$.
