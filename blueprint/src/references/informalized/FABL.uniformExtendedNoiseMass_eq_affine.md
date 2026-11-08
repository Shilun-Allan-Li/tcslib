<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedNoiseExtensions.lean :: FABL.uniformExtendedNoiseMass_eq_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine formula for noise mass

**Claim.** The extended noise mass from $x$ to $y$ is the sum of a diagonal contribution of $ho$ and the uniform contribution $(1-ho)/|\Omega|$.

**Proof.** Split into the cases $y=x$ and $y\ne x$. On the diagonal, the diagonal formula for the extended noise mass gives $\rho+(1-\rho)/|\Omega|$ (`uniformExtendedNoiseMass_self`), which is the claimed expression because the indicator is $1$. Off the diagonal, its off-diagonal formula gives $(1-\rho)/|\Omega|$ (`uniformExtendedNoiseMass_of_ne`), and the indicator is $0$. These are exactly the two cases of the affine formula.

**Key facts.** `FABL.uniformExtendedNoiseMass_self`, `FABL.uniformExtendedNoiseMass_of_ne`.
