<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_contract -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Noise Contraction

**Claim.** For $\rho\in[-1,1]$, $p\ge1$, and $f$ in Gaussian $L^p$, the $L^p$ seminorm of its Gaussian noise image is at most that of $f$.

**Proof.** View the noise image as the average, over the second Gaussian vector, of the function $f$ evaluated at the Gaussian endpoint $\rho x+\sqrt{1-\rho^2}\,y$. Since $p\ge1$, the integral form of the $L^p$ triangle inequality (\texttt{eLpNorm_integral_prod_le}) bounds the seminorm of this average by the seminorm of the two-variable endpoint composition. The endpoint map preserves Gaussian measure ($\texttt{measurePreserving_gaussianEndpoint}$), so composing $f$ with it leaves its $L^p$ seminorm unchanged. Combining the two statements proves contraction.

**Key facts.** `BooleanAnalysis.GaussianSpace.eLpNorm_integral_prod_le`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`.
