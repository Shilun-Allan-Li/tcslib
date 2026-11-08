<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: BooleanAnalysis.Hypercontractivity.two_point_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Two-point norm inequality

**Claim.** For $1\le p\le2$, $0\le\rho$, and $\rho^2\le p-1$, the two-point norm of $(a+\rho b x)$ is at most the $p$-norm of $(a+b x)$, expressed by the inequality in the formal statement.

**Proof.** First prove a homogeneous inequality under the normalization $a\ge0$ and $|b|\le a$: raise the desired norm comparison to the power $p$ and use the corresponding power inequality with coefficient $p-1$. To reduce arbitrary $a,b$, split according to whether $|a|\ge|b|$. In that case, choose the sign of $a$ and use symmetry of the two values to reduce to $a\ge0$, $|b|\le a$; the absolute values disappear because both $a+b$ and $a-b$ are nonnegative. If $|a|<|b|$, interchange the roles of $a$ and $b$ in the symmetric two-point expression; the resulting bound compares the left side by monotonicity of positive powers, and the already established normalized case applies. Now handle the normalized inequality. If $a=0$, then $b=0$ and the claim follows directly. Otherwise divide by $a$ and apply homogeneity, reducing to $a=1$ and $|b|\le1$. For $b\ge0$, apply the one-sided unit inequality (BooleanAnalysis.Hypercontractivity.two_point_ineq_unit); for $b<0$, apply it to $-b$ and use the symmetry exchanging the two points. This gives the power inequality at coefficient $p-1$. Finally, the assumption $\rho^2\le p-1$ and nonnegativity of the relevant bases allow replacing $p-1$ by $\rho^2$ on the left, and taking the appropriate positive power roots yields the stated norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.two_point_ineq_unit`.

**Caveat.** The proof source’s non-normalized reduction for $|a|<|b|$ invokes power monotonicity and the normalized bound in a compressed sequence; the intervening comparison is not fully transparent from the supplied proof.
