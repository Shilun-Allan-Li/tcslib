<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean :: concentration_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration Bound at the Zero Vector

**Claim.** For any matrix family and any real $\varepsilon$, the probability that the zero vector triggers the bad distortion event is at most $2\exp(-k\varepsilon^2/8)$.

**Proof.** At the zero vector, both its norm and the norm of its image under every linear map are zero. Thus the strict inequality defining the bad event becomes $0<0$, which is false for every outcome. The event is empty, so its probability is zero, and zero is at most the stated nonnegative exponential bound.
