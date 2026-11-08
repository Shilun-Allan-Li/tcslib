<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanCharacteristic.lean :: BooleanAnalysis.GaussianSpace.sum_correlatedSign_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Sign Phase Sum

**Claim.** The sum over the two Boolean signs in each coordinate of the weighted complex phase equals the complex embedding of $\frac{1+\rho}{2}\cos(a+b)+\frac{1-\rho}{2}\cos(a-b)$.

**Proof.** There are four pairs of Boolean inputs, and their signs are respectively $(1,1)$, $(1,-1)$, $(-1,1)$, and $(-1,-1)$. Substituting these values into the sum, and using that $e^{iu}=\cos u+i\sin u$ for real $u$, the terms pair with their negatives: the imaginary parts cancel. The two equal-sign pairs contribute the cosine at $a+b$, with combined weight $(1+\rho)/2$; the two opposite-sign pairs contribute the cosine at $a-b$, with combined weight $(1-\rho)/2$. This is exactly the stated characteristic expression.
