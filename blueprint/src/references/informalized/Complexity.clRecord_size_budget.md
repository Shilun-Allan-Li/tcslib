<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecord_size_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic size bound

**Claim.** If $T\le n$, then $2n+8+k(3n+7)+(8l+7)(T+1)^2$ is at most $(10+10k+(8l+7))(n+1)^2$.

**Proof.** Since $T\le n$, we have $(T+1)^2\le(n+1)^2$. Also $n+1\le(n+1)^2$ for natural $n$, and elementary arithmetic gives $2n+8\le10(n+1)^2$ and $3n+7\le10(n+1)^2$. Multiply the latter two bounds by $1$ and $k$, respectively, and multiply the squared bound by $8l+7$. Adding these inequalities yields the result.
