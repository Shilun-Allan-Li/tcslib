<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: hasBernsteinMGF_centered_chi_squared -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernstein MGF for centered Gaussian squares

**Claim.** If $Y$ has Gaussian law with mean zero and variance $1/k$, where $k>0$, then $Y^2-1/k$ satisfies the stated Bernstein MGF bounds with parameters $c=2/k^2$ and $t_{\max}=k/4$.

**Proof.** To verify the two requirements in the definition of the Bernstein MGF property, fix any real $t$ with $|t|\le k/4$. The centered chi-squared estimate `centered_chi_squared_step`, applied using the assumed Gaussian law of $Y$, gives both integrability of $\exp(t(Y^2-1/k))$ and the bound on its MGF by $\exp(2t^2/k^2)$. The latter exponent is exactly $ct^2$ for $c=2/k^2$, so these two conclusions establish the required property.

**Key facts.** `centered_chi_squared_step`.
