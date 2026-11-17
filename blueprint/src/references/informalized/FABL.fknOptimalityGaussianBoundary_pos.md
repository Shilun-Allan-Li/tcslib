<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianBoundary_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Gaussian Boundary

**Claim.** For every $q\in\mathbb{N}$, the Gaussian boundary associated with $q$ is strictly positive.

**Proof.** First express the Gaussian boundary as the standard Gaussian density at the threshold associated with $q$ (`fknOptimalityGaussianBoundary_eq_density`). The standard Gaussian density is strictly positive at every real argument, so its value at this threshold is positive. Hence the boundary is positive.

**Key facts.** `FABL.fknOptimalityGaussianBoundary_eq_density`.
