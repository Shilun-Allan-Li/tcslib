<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radJointMeasure_row_marginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row Marginal of the Joint Measure

**Claim.** The distribution of any fixed row of the joint Rademacher array is the product of $d$ Rademacher distributions.

**Proof.** The joint array measure is the product, over row indices, of the row measures, each of which is itself the product of $d$ copies of `rademacherReal`. Under a product measure, projection onto a coordinate has as its pushforward the corresponding coordinate measure. Applying this coordinate projection property to the fixed row gives the asserted row marginal.
