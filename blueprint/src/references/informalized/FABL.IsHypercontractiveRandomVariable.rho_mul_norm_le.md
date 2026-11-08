<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.IsHypercontractiveRandomVariable.rho_mul_norm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parameter Times Norm Bound

**Claim.** If $q\ne0$, $\rho\ge0$, and the hypercontractive inequality holds from $p$ to $q$ with parameter $\rho$, then $\rho$ times the uniform $q$-norm of $X$ is at most its uniform $p$-norm.

**Proof.** Apply the assumed inequality with $a=0$ and $b=1$. The resulting left-hand norm is that of $\rho X$. Homogeneity gives $\|\rho X\|_q=|\rho|\|X\|_q$ (`uniformLpNormENNReal_const_mul`); since $\rho\ge0$, this is $\rho\|X\|_q$. The right-hand side is the uniform $p$-norm of $X$, yielding the result.

**Key facts.** `FABL.uniformLpNormENNReal_const_mul`.
