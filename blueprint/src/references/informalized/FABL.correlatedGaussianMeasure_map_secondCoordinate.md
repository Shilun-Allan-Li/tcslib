<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.correlatedGaussianMeasure_map_secondCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Gaussian marginal

**Claim.** If $-1\leq\rho\leq1$, the second coordinate of the correlated pair has the standard Gaussian law.

**Proof.** We show that the two measures have the same characteristic function at each real test value $t$. The characteristic function of the second-coordinate image is the characteristic function of the correlated measure tested against the plane vector $(0,t)$: the inner product with this vector extracts $t$ times the second coordinate. The correlated measure's characteristic function is $\exp(-Q_\rho(0,t)/2)$ (`charFun_correlatedGaussianMeasure`). Substitution into the quadratic form gives $Q_\rho(0,t)=t^2$. This is exactly the characteristic function of a standard Gaussian (`charFun_gaussianReal`). Uniqueness of characteristic functions proves the marginal identity.

**Key facts.** `FABL.continuous_correlationSecondCoordinate`, `FABL.charFun_correlatedGaussianMeasure`.
