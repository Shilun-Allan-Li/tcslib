<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.isOpen_angularDisagreementSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Openness of the angular disagreement set

**Claim.** For every real $\alpha$, the set of angles in $(-\pi,\pi)$ satisfying $\cos\theta\,\cos(\theta-\alpha)<0$ is open in $\mathbb R$.

**Proof.** The function $\theta\mapsto\cos\theta\cos(\theta-\alpha)$ is continuous, since cosine, translation by the fixed angle, and multiplication are continuous. The set where this function is strictly less than zero is therefore open. Intersecting it with the open interval $(-\pi,\pi)$ gives the stated angular disagreement set, which is open.
