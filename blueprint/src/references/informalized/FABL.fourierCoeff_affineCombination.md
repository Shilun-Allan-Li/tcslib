<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierSquareConvexity.lean :: FABL.fourierCoeff_affineCombination -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Linearity of Fourier Coefficients

**Claim.** The Fourier coefficient of the pointwise affine combination $\theta f+(1-\theta)g$ is $\theta\widehat f(S)+(1-\theta)\widehat g(S)$.

**Proof.** In the defining expectation, distribute multiplication by the monomial across the sum: the integrand becomes $\theta f(x)\chi_S(x)+(1-\theta)g(x)\chi_S(x)$. Linearity of uniform expectation splits this into the sum of the two expectations. Since expectation also commutes with multiplication by a constant, these are exactly $\theta\widehat f(S)$ and $(1-\theta)\widehat g(S)$.
