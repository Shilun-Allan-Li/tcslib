<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.matchingStirlingCore_eq_constant_mul_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact matching core factorization

**Claim.** For positive integers $r$ and $k$, the matching Stirling core equals $\sqrt r\,(2\pi)^{(1-r)/2}$ times the matching core growth.

**Proof.** Set $B=2k\pi$ and $\beta=(1-r)/2$. Positivity of $r,k$ and $\pi$ gives $B>0$. The numerator inside the square root is $rB$, so its square root is $\sqrt r\sqrt B$. Since $\sqrt B=B^{1/2}$ and $\sqrt B^{\,r}=B^{r/2}$, their quotient contributes $B^{1/2-r/2}=B^\beta$. Finally, write $B=(2\pi)k$ and use the product rule for real powers of nonnegative bases to obtain $B^\beta=(2\pi)^\beta k^\beta$. The factor $k^\beta$ is the matching core growth, leaving the stated constant factor.
