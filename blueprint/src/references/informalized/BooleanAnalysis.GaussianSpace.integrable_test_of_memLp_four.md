<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.integrable_test_of_memLp_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability under fourth moment control

**Claim.** If $Z$ belongs to $L^4$ on a probability space and $\psi$ is four times continuously differentiable with bounded fourth derivative, then $\psi\circ Z$ is integrable.

**Proof.** Apply the general Taylor-remainder integrability result `integrable_test_of_memLp` with $m=3$. Then $m+1=4$, so the assumed $L^4$ condition, fourfold continuous differentiability, and uniform bound on the fourth derivative are exactly its hypotheses. It follows that $\psi(Z)$ is integrable.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_test_of_memLp`.
