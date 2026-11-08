<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.gaussianIsoperimetric_second_derivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Derivative Identity

**Claim.** For every α in (0,1), the second derivative of the real-valued Gaussian isoperimetric function at α equals the negative reciprocal of its value there.

**Proof.** Fix α in (0,1). The upper quantile, viewed as a real-valued function on all of ℝ with its prescribed interior expression, has derivative equal to the negative reciprocal of the Gaussian isoperimetric function at α (hasDerivAt_standardGaussianUpperQuantileReal). On a neighborhood of α contained in (0,1), the quantile agrees with the interior quantile expression (standardGaussianUpperQuantileReal_eq). The Gaussian isoperimetric function has derivative there equal to that interior quantile (hasDerivAt_gaussianIsoperimetricReal). Consequently the derivative of the Gaussian isoperimetric function itself has derivative at α equal to the derivative of the quantile, namely the negative reciprocal of the profile. Rewriting this derivative as the second iterate of differentiation gives the stated identity.

**Key facts.** `FABL.hasDerivAt_standardGaussianUpperQuantileReal`, `FABL.standardGaussianUpperQuantileReal_eq`, `FABL.hasDerivAt_gaussianIsoperimetricReal`.
