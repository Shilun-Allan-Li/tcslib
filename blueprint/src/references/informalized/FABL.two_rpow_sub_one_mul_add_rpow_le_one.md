<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.two_rpow_sub_one_mul_add_rpow_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power bound for two parts

**Claim.** If $a,b\ge0$, $a+b=1$, and $0\le r\le1$, then $2^{r-1}(a^r+b^r)\le1$.

**Proof.** The function $x\mapsto x^r$ is concave on the nonnegative reals for $0\le r\le1$ (`Real.concaveOn_rpow`). Applying midpoint concavity to $a$ and $b$ gives $((a+b)/2)^r\ge(a^r+b^r)/2$. Since $a+b=1$, this implies $a^r+b^r\le2(1/2)^r$. For nonnegative powers, $(1/2)^r=2^{-r}$, and thus $2^{r-1}\cdot2\cdot2^{-r}=1$. Multiplying the preceding bound by the nonnegative factor $2^{r-1}$ proves the result.
