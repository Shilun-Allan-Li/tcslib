<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.diag_cost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic overhead bound

**Claim.** For all natural numbers $n,T,c_0,c_1,C$, the displayed left-hand expression is at most the displayed constant multiple of $(T+n+1)^2$.

**Proof.** Set $X=T+n+1$. Since $X\ge1$, we have $X\le X^2$ and $1\le X^2$. Also $c_0T+1\le(c_0+1)X$: indeed, $c_0T\le c_0X$ and $1\le X$. Squaring gives $(c_0T+1)^2\le(c_0+1)^2X^2$. Multiplying by $c_1$ and using $1\le X^2$ yields $c_1(c_0T+1)^2+1\le(c_1(c_0+1)^2+1)X^2$. Multiply this inequality by $C$. Finally, $5n+7\le8X^2$ because $X\ge n+1$ and $8(n+1)^2\ge5n+7$. Adding the two bounds proves the result.
