<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.normalized_pTwo_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Two-Point Power Inequality

**Claim.** If $1\le p\le2$ and $|e|\le1$, then $\sqrt{1+(p-1)e^2}\le\left(((1+e)^p+(1-e)^p)/2\right)^{1/p}$.

**Proof.** The quantity $s=(p-1)e^2$ is nonnegative, and $p/2$ lies in $[0,1]$. The inequality $(1+s)^\theta\le1+\theta s$ for $s\ge0$ and $0\le\theta\le1$ therefore gives $(1+(p-1)e^2)^{p/2}\le1+p(p-1)e^2/2$. The two-point average bound (`average_rpow_lower_quadratic`) says that this last expression is at most $((1+e)^p+(1-e)^p)/2$. Raising both nonnegative sides to the power $1/p$ preserves the inequality. Since $(p/2)(1/p)=1/2$, the left side becomes $\sqrt{1+(p-1)e^2}$, yielding the result.

**Key facts.** `FABL.average_rpow_lower_quadratic`.
