<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: integral_sq_rademacherReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment of the Rademacher distribution

**Claim.** The second moment of the equally weighted distribution on $-1$ and $+1$ is one.

**Proof.** Expand the integral over the two weighted point masses. Integrating $y^2$ against a point mass at $a$ gives $a^2$, and each mass has weight $1/2$. Both support points have square one, so the two contributions sum to $\tfrac12+\tfrac12=1$.

**Key facts.** `integrable_smul_dirac`.
