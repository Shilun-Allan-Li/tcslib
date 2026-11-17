<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.gaussianNoise_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjointness of Gaussian noise

**Claim.** For square-integrable $f,g$ and a correlation $\rho\in[-1,1]$, the Gaussian inner product of $f$ with $T_\rho g$ equals that of $T_\rho f$ with $g$.

**Proof.** Represent the first integral as an integral over the correlated Gaussian pair: the expectation of $f$ on the first coordinate times $g$ on the second equals the integral of $fT_\rho g$ (\texttt{integral\_correlatedGaussianMeasure}). The correlated Gaussian law is invariant under swapping the two coordinates (\texttt{correlatedGaussianMeasure\_swap}). Changing variables by this swap changes the integrand to $g$ on the first coordinate times $f$ on the second. Applying the same integral representation with $g$ and $f$ interchanged turns this into the integral of $gT_\rho f$. Commutativity of multiplication gives the desired order of factors.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_swap`.
