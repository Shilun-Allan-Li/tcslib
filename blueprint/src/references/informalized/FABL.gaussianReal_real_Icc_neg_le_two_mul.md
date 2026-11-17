<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.gaussianReal_real_Icc_neg_le_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian mass of a symmetric interval

**Claim.** For every $t\ge 0$, the standard Gaussian measure of $[-t,t]$ is at most $2t$.

**Proof.** Express the Gaussian measure of the interval as the integral of its density over $[-t,t]$. The density is nonnegative, so this integral is the real-valued measure of the interval. By the pointwise bound $\text{gaussianPDFReal}(0,1,x)\le 1$ (`FABL.gaussianPDFReal_zero_one_le_one`), the integral is at most the integral of the constant function $1$. That integral is the interval's length, $t-(-t)=2t$, using $t\ge0$.

**Key facts.** `FABL.gaussianPDFReal_zero_one_le_one`.
