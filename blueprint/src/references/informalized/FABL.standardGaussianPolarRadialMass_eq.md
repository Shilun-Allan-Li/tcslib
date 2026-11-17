<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.standardGaussianPolarRadialMass_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total radial mass

**Claim.** The total radial mass of the planar standard Gaussian in polar coordinates is $(2\pi)^{-1}$.

**Proof.** Apply the angular-event formula to the whole plane and to the full angular interval $(-\pi,\pi)$. Every point in the polar-coordinate target belongs to the plane, and every angle in that target lies in this interval, so the formula gives $1=M\,|(-\pi,\pi)|$, where $M$ is the total radial mass. The interval has length $2\pi$, hence $1=M(2\pi)$. Solving for $M$ gives $(2\pi)^{-1}$.

**Key facts.** `FABL.standardGaussianPlane_measure_angularEvent`.
