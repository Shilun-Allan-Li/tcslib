<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.isOpen_gaussianSourceDisagreement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Openness of the Gaussian source disagreement set

**Claim.** For each real $\rho$, the set of pairs $(u,v)$ satisfying $u\bigl(\rho u+\sqrt{1-\rho^2}\,v\bigr)<0$ is open.

**Proof.** For fixed $\rho$, the expression $u\bigl(\rho u+\sqrt{1-\rho^2}\,v\bigr)$ is continuous as a function of $(u,v)$: it is formed from coordinate projections, multiplication, and addition with fixed real coefficients. The set where this continuous function is strictly below zero is open, which is the claimed disagreement set.
