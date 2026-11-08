<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clQuery_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound for Query Cost

**Claim.** If $N\le L$, then the query-cost expression is at most $(100(l+10)+c)(L+1)^{e+2}$.

**Proof.** Use $N\le L$ to bound the term multiplied by $N$ by the same term multiplied by $L$. Expanding and collecting the resulting polynomial terms shows that the non-polynomial-machine portion, including the final additive constant $2$, is at most $100(l+10)(L+1)^2$. Since $L+1\ge1$ and $e+2\ge2$, this is at most $100(l+10)(L+1)^{e+2}$. Also $N+1\le L+1$, so monotonicity of natural-number powers gives $(N+1)^e\le(L+1)^e\le(L+1)^{e+2}$. Multiplying by $c$ and adding the two bounds yields the desired inequality.
