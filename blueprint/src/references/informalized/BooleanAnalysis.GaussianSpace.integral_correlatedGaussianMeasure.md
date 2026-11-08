<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Gaussian integration

**Claim.** For $\rho\in[-1,1]$ and $f,g\in L^2(\gamma_n)$, the integral of $f(x)g(y)$ under the correlated Gaussian law equals the integral under $\gamma_n$ of $f(x)$ times the Gaussian noise average of $g$ at $x$.

**Proof.** The proof first uses the $L^2$ hypotheses and the bound on $\rho$ to obtain integrability of $(x,y)\mapsto f(x)g(y)$ under the correlated Gaussian measure (\texttt{integrable_correlatedGaussianMeasure_mul}). The integral formula for integrable products (\texttt{integral_correlatedGaussianMeasure_of_integrable}) then gives the stated equality.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_correlatedGaussianMeasure_mul`, `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure_of_integrable`.
