<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.volume_angularDisagreementSet_of_le_half_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small-Angle Disagreement Measure

**Claim.** For $0\leq\alpha\leq\pi/2$, the angles in $(-\pi,\pi)$ for which $\cos\theta$ and $\cos(\theta-\alpha)$ have opposite signs have Lebesgue measure $2\alpha$.

**Proof.** The disagreement set is the union of the intervals $(-\pi/2,\alpha-\pi/2)$ and $(\pi/2,\alpha+\pi/2)$ (\texttt{angularDisagreementSet\_eq\_of\_le\_half\_pi}). They are disjoint in the stated range. Each has length $\alpha$, so additivity of Lebesgue measure gives total measure $2\alpha$.

**Key facts.** `FABL.angularDisagreementSet_eq_of_le_half_pi`.
