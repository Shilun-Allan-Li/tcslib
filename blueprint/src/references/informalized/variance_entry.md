<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: variance_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Rademacher Entry

**Claim.** Every coordinate of the independent Rademacher array has variance $1$.

**Proof.** The coordinate projection is measurable. Its distribution is the one-dimensional Rademacher measure, because the coordinate marginal of the product measure is that measure (radJointMeasure_entry_marginal). Variance is preserved under this identification of the distribution, and the identity random variable under the Rademacher measure has variance $1$ (variance_id_rademacherReal).

**Key facts.** `radJointMeasure_entry_marginal`, `variance_id_rademacherReal`.
