<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.kkl_coefficient_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# KKL coefficient identity

**Claim.** For $\lambda,V,I>0$, $\left(\frac{V(\sqrt{\lambda}/3)^{I/V}}{I}\right)^2=\left((I/V)^{-1}\right)^2(9/\lambda)^{-I/V}$.

**Proof.** Let $\rho=\sqrt{\lambda}/3$. Then $\rho\ge0$ and $\rho^2=\lambda/9=(9/\lambda)^{-1}$. The laws of real powers give $(\rho^{I/V})^2=(\rho^2)^{I/V}=(9/\lambda)^{-I/V}$. Squaring the coefficient on the left of the claim and separating its factors leaves $\bigl(V/I\bigr)^2(\rho^{I/V})^2$. Since $V/I=(I/V)^{-1}$, the preceding power identity yields exactly the right-hand side.
