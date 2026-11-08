<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.one_sub_pow_le_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Probability Bound

**Claim.** If $x$ is rational with $0\le x\le1$ and $m$ is a natural number such that $mx\ge1$, then $(1-x)^m\le1/2$.

**Proof.** We prove by induction on $m'$ that $(1-x)^{m'}(1+m'x)\le1$. It is equality at $m'=0$. For the step, the factor identity $(1-x)(1+(m'+1)x)=1+m'x-(m'+1)x^2$ shows that this factor is at most $1+m'x$, since $(m'+1)x^2\ge0$. Also $(1-x)^{m'}\ge0$, so multiplying preserves the inequality; the induction hypothesis then proves the bound at $m'+1$. Now take $m'=m$. The assumption $mx\ge1$ gives $1+mx\ge2$, and the established inequality implies $(1-x)^m\le1/(1+mx)\le1/2$.
