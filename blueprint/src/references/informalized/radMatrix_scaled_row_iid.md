<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radMatrix_scaled_row_iid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of scaled row entries

**Claim.** For any fixed row, the entries obtained by multiplying each column entry by its corresponding factor $x_j/\sqrt{k}$ are mutually independent under the product Rademacher measure.

**Proof.** The entries in the chosen row are mutually independent by the row-independence property of the product measure (`radJointMeasure_row_iid`). Applying a deterministic measurable function separately to each entry preserves mutual independence. Here the function in column $j$ is multiplication by the constant $x_j/\sqrt{k}$, which is measurable, so the scaled entries remain mutually independent.

**Key facts.** `radJointMeasure_row_iid`.
