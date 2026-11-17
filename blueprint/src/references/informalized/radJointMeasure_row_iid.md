<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radJointMeasure_row_iid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence Within a Rademacher Row

**Claim.** For a fixed row index, its coordinate maps are mutually independent under the joint Rademacher measure.

**Proof.** Mutual independence is characterized by equality between the joint law of the vector of coordinate maps and the product of their individual marginal laws. The vector of entries in the fixed row is precisely the row projection, whose law is the product Rademacher measure by the row marginal fact (`radJointMeasure_row_marginal`). Each individual coordinate has law `rademacherReal` by the entry marginal fact (`radJointMeasure_entry_marginal`), so the product of the individual marginals is the same product measure. This verifies the characterization and proves independence.

**Key facts.** `radJointMeasure_entry_marginal`, `radJointMeasure_row_marginal`.
