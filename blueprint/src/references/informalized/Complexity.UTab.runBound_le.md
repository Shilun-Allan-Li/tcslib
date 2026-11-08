<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.runBound_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Bound on the Run Length

**Claim.** With $L,K,S,A,$ and $B$ as specified, the bound $B+(T+1)(A+7T+10)+L+2\le 60(k+1)(L+30)(n+T+|z|+3)^3$ holds.

**Proof.** Set $X=n+T+|z|+3$, $K=L+30$, and $Y=(k+1)KX^2$. Since $X,K\ge1$, we have $KX\le Y$. The stride satisfies $S\le(2k+1)X$, by expanding its definition and bounding each summand using the terms in $X$. We next bound the layer quantity $A$ term by term: its first term is at most $3Y$, its second at most $Y$, and its term $9(T+1)S$ at most $27Y$. The remaining constant and $K$ contribution is at most $Y$, so altogether $A\le32Y$. Also $T+1\le X$ and $7T+10\le17Y$, hence $(T+1)(A+7T+10)\le49XY$. The prefix contribution together with $L+2$ is at most $5KX$. Combining these estimates gives the left side at most $49XY+5KX$. Since $X,K\ge1$ and $k+1\ge1$, this is at most $60(k+1)KX^3$. Substituting $K=L+30$ and the definition of $X$ yields the claimed cubic bound.
