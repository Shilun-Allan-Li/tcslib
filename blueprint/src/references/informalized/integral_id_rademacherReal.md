<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integral_id_rademacherReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Rademacher distribution

**Claim.** The mean of the equally weighted distribution on $-1$ and $+1$ is zero.

**Proof.** Expand the integral over the sum of the two point masses. The integral of the identity against a point mass at $a$ is its value $a$, and scaling a measure scales the integral by the same weight. The two contributions are therefore $\tfrac12(-1)$ and $\tfrac12(1)$, which sum to zero.

**Key facts.** `integrable_smul_dirac`.
