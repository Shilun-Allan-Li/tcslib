<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.volume_angularDisagreementSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Angular Disagreement Measure

**Claim.** For $0\leq\alpha\leq\pi$, the angles in $(-\pi,\pi)$ for which $\cos\theta$ and $\cos(\theta-\alpha)$ have opposite signs have Lebesgue measure $2\alpha$.

**Proof.** Split into the cases $\alpha\leq\pi/2$ and $\pi/2\leq\alpha$. In the first case, the small-angle interval decomposition and measure computation establish the claimed measure (\texttt{volume\_angularDisagreementSet\_of\_le\_half\_pi}). In the second case, the corresponding large-angle decomposition and measure computation establish the same formula (\texttt{volume\_angularDisagreementSet\_of\_half\_pi\_le}). The cases cover the full assumed range, so the result follows.

**Key facts.** `FABL.volume_angularDisagreementSet_of_le_half_pi`, `FABL.volume_angularDisagreementSet_of_half_pi_le`.
