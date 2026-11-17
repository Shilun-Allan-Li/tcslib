<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.pmfExpectation_uniformExtendedCoordinateNoisePMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under Extended Coordinate Noise

**Claim.** For the stated range of $\rho$, the expectation of $f$ under the extended coordinate noise distribution centered at $x$ is $\rho f(x)+(1-\rho)$ times the uniform average of $f$.

**Proof.** Expand the expectation as a finite sum of point masses times function values. The mass at each $y$ is an affine expression in the point indicator of $x$: it equals $\rho\mathbf{1}_{\{x\}}(y)+(1-\rho)/|\Omega|$ (`uniformExtendedNoiseMass_eq_affine`); the point-mass formula for the constructed distribution identifies its real-valued mass with this expression (`uniformExtendedCoordinateNoisePMF_apply_toReal`). Distribute the product with $f(y)$ and sum. The indicator term contributes $\rho f(x)$, while the constant-weight term is $(1-\rho)/|\Omega|$ times $\sum_y f(y)$. Recognizing the latter as $(1-\rho)$ times the uniform average gives the result.

**Key facts.** `FABL.uniformExtendedCoordinateNoisePMF_apply_toReal`, `FABL.uniformExtendedNoiseMass_eq_affine`.
