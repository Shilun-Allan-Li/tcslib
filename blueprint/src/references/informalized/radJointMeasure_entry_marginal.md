<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radJointMeasure_entry_marginal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marginal Law of a Matrix Entry

**Claim.** For any row and column indices, the coordinate projection of the joint Rademacher measure has distribution equal to the Rademacher measure.

**Proof.** First project the joint array measure to its fixed row. The row marginal is the product measure of the $d$ Rademacher coordinates (the row marginal fact, `radJointMeasure_row_marginal`). Under that product measure, projection onto coordinate $j$ has distribution `rademacherReal`, by the coordinate projection property of a product measure. Since the entry projection factors as row projection followed by this coordinate projection, the pushforward composition formula gives the claimed marginal.

**Key facts.** `radJointMeasure_row_marginal`.
