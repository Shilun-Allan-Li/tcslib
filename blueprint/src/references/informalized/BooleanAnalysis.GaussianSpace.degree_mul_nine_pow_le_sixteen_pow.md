<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance.lean :: BooleanAnalysis.GaussianSpace.degree_mul_nine_pow_le_sixteen_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound on the degree factor

**Claim.** For every natural number $k$, $k9^k\le16^k$.

**Proof.** The cases $k=0$ and $k=1$ follow by direct calculation. For $k\ge2$, write $k=m+2$ and prove the bound by induction on $m$. The base case $m=0$ is a direct calculation. For the induction step, observe that $9(m+3)\le16(m+2)$, since the difference of the right and left sides is $7m+5\ge0$. Multiplying this inequality by the nonnegative factor $9^{m+2}$ gives $(m+3)9^{m+3}\le16(m+2)9^{m+2}$. The induction hypothesis bounds the latter by $16\cdot16^{m+2}=16^{m+3}$, completing the step.
