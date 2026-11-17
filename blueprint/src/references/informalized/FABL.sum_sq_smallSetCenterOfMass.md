<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallSetCenterOfMass.lean :: FABL.sum_sq_smallSetCenterOfMass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Center-of-Mass Squared Norm

**Claim.** For a real-valued function on the sign cube and any real scale parameter, the squared norm of its small-set center of mass equals its level-one Fourier weight divided by the square of the parameter, with real division interpreted in its usual totalized sense.

**Proof.** By the coordinate formula for the small-set center of mass (`FABL.smallSetCenterOfMass_apply`), its coordinate at $i$ is the singleton Fourier coefficient divided by $\alpha$. Squaring and summing over coordinates therefore gives $\sum_i \widehat f(\{i\})^2/\alpha^2$. Factoring out the common denominator yields $(\sum_i \widehat f(\{i\})^2)/\alpha^2$. The level-one weight is exactly this sum of singleton coefficient squares (`FABL.fourierWeightAtLevel_one_eq_sum_singleton`), giving the claimed identity. The algebra remains valid at $\alpha=0$ under totalized real division.

**Key facts.** `FABL.smallSetCenterOfMass_apply`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
