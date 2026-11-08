<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedSignPairPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Point probabilities of the correlated sign law

**Claim.** The probability assigned to $(x,y)$ by the correlated sign law is the uniform probability of $x$ multiplied by the conditional noise probability of obtaining $y$ from $x$.

**Proof.** Expand the law as the bind of the uniform first-sign distribution with the noise distribution, followed by the map that records the pair. In the finite sum for the probability of $(x,y)$, only the term with initial sign $x$ can contribute, and within that term only the noise outcome $y$ contributes. The resulting product is the uniform probability of $x$ times the conditional noise probability of $y$ given $x$.
