<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.standardGaussianPlane_measure_angularEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Angular events under the planar Gaussian

**Claim.** If a measurable set in the plane is described in polar coordinates by an angular set $A\subseteq(-\pi,\pi)$, then its product standard Gaussian measure is the total radial mass times the Lebesgue measure of $A$.

**Proof.** Write the planar standard Gaussian as a density with respect to area measure, then change variables to polar coordinates. On the polar-coordinate target, the hypothesis says that membership in the set is equivalent to the angle belonging to $A$. Thus the transformed integrand, including the polar Jacobian, is the radial density multiplied by the indicator of angles in $A$: the polar form of the planar density is exactly the stated radial density (\texttt{standardGaussianPlaneDensity\_polar}). The angular restriction of the polar target is precisely $(0,\infty)\times A$, since $A$ lies between $-\pi$ and $\pi$. Integrating over this product separates the radial and angular variables. The radial factor is the integral of the radial density over positive radii, and the angular factor is the Lebesgue measure of $A$, giving the formula.

**Key facts.** `FABL.standardGaussianPlane_eq_withDensity`, `FABL.standardGaussianPlaneDensity_polar`.
