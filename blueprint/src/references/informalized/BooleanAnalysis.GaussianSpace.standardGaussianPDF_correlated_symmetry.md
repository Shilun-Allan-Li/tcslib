<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/ProfileCalculus.lean :: BooleanAnalysis.GaussianSpace.standardGaussianPDF_correlated_symmetry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Correlated Gaussian Densities

**Claim.** If $s\ne0$ and $s^2=1-\rho^2$, then $\varphi((b-\rho a)/s)\varphi(a)=\varphi((a-\rho b)/s)\varphi(b)$.

**Proof.** Using the formula for the standard Gaussian density, $\varphi(x)=(\sqrt{2\pi})^{-1}e^{-x^2/2}$ (`BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`), both sides have the same constant factor $(\sqrt{2\pi})^{-2}$. It remains to compare their exponents. Expanding and clearing the nonzero denominator $s$ reduces the equality to an algebraic identity whose difference is a multiple of $s^2-(1-\rho^2)$. The hypothesis makes this difference zero, so the exponents agree and therefore the density products agree.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_eq`.
