<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallSetCenterOfMass.lean :: FABL.exists_smallSetCenterOfMass_sqNorm_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Center of Mass Bound

**Claim.** For the stated indicator-valued function and density $\alpha$, the sum of the squared center-of-mass coordinates is bounded by a constant times $\log_2(1/\alpha)$.

**Proof.** Use the positive constant from the level-one Fourier-weight estimate. The identity for the center of mass expresses the sum of its squared coordinates as the level-one Fourier weight divided by $\alpha^2$. Apply the level-one estimate to bound that weight by $C\alpha^2\log_2(1/\alpha)$. Since $\alpha>0$, division by $\alpha^2$ is valid; canceling this factor and rearranging gives the claimed bound.

**Key facts.** `FABL.exists_levelOneInequality_constant`, `FABL.sum_sq_smallSetCenterOfMass`.
