<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_size_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Count Budget

**Claim.** If $T\le n$, $R\le T$, and $a\le 2n+4+k(3n+7)+(4l+7)(T+1)^2$, then $a+R+4\le (10+10k+8l+7)(n+1)^2$.

**Proof.** Use $T\le n$ to bound $(T+1)^2$ by $(n+1)^2$, and use $R\le T\le n$. The linear terms satisfy $2n+8+R\le 3n+8\le 10(n+1)^2$. Also $3n+7\le 10(n+1)^2$, so multiplying by $k$ bounds the $k(3n+7)$ contribution by $10k(n+1)^2$. Finally, $(4l+7)(T+1)^2\le (4l+7)(n+1)^2$. Adding these bounds gives coefficient $10+10k+4l+7$, which is at most $10+10k+8l+7$ for natural $l$. The assumed bound on $a$ now yields the result; the displayed $a+0+R+4$ is the same left side.
