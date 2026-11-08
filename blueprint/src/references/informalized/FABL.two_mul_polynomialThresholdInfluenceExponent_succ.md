<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdInfluence.lean :: FABL.two_mul_polynomialThresholdInfluenceExponent_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recurrence for the influence exponent

**Claim.** For every nonnegative integer $k$, if $a_k=1-2^{-k}$, then $2a_{k+1}=1+a_k$.

**Proof.** By definition, $a_k=1-(2^k)^{-1}$. Also, $2^{k+1}=2\cdot2^k$, so $a_{k+1}=1-(2\cdot2^k)^{-1}$. Since $2^k\ne0$, elementary fraction arithmetic gives $2a_{k+1}=2-(2^k)^{-1}=1+a_k$.
