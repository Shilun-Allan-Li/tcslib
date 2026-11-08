<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.volume_angularDisagreementSet_of_half_pi_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Large-Angle Disagreement Measure

**Claim.** For $\pi/2\leq\alpha\leq\pi$, the angles in $(-\pi,\pi)$ for which $\cos\theta$ and $\cos(\theta-\alpha)$ have opposite signs have Lebesgue measure $2\alpha$.

**Proof.** The disagreement set is the union of three open intervals: $(-\pi,\alpha-3\pi/2)$, $(-\pi/2,\alpha-\pi/2)$, and $(\pi/2,\pi)$ (\texttt{angularDisagreementSet\_eq\_of\_half\_pi\_le}). The interval bounds and $\pi/2\leq\alpha\leq\pi$ show these intervals are pairwise disjoint. Their lengths are respectively $\alpha-\pi/2$, $\alpha$, and $\pi/2$. Additivity of Lebesgue measure on disjoint measurable intervals gives total measure $(\alpha-\pi/2)+\alpha+\pi/2=2\alpha$.

**Key facts.** `FABL.angularDisagreementSet_eq_of_half_pi_le`.
