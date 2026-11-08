<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.expect_mul_fourth_le_expect_sq_cubed_mul_expect_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment Product Bound

**Claim.** If $g^3=g$ and $g^4=g^2$ pointwise, then $(\mathbb E[gh])^4\le(\mathbb E[g^2])^3\mathbb E[h^4]$.

**Proof.** Write $\alpha=\mathbb E[g^2]$, $B=\mathbb E[g^2h^2]$, and $H_4=\mathbb E[h^4]$. These three quantities are nonnegative; in particular, expectations of squares and fourth powers are nonnegative (`expect_sq_nonneg`, `expect_fourth_nonneg`). Apply Cauchy–Schwarz for finite averages first to $g^2$ and $gh$. Since $g^3=g$ and $g^4=g^2$, this gives $(\mathbb E[gh])^2\le\alpha B$. Apply it again to $g$ and $gh^2$ to get $B^2\le\alpha\mathbb E[g^2h^4]$. Pointwise, $g^2\le1$: indeed $(g^2)^2=g^2$ implies $g^2$ is either $0$ or $1$. Thus $g^2h^4\le h^4$, and averaging yields $B^2\le\alpha H_4$. Squaring the first estimate and then using the second, with nonnegativity to preserve the inequalities, gives $(\mathbb E[gh])^4\le(\alpha B)^2\le\alpha^3H_4$, which is the desired bound.

**Key facts.** `FABL.expect_sq_nonneg`, `FABL.expect_fourth_nonneg`.
