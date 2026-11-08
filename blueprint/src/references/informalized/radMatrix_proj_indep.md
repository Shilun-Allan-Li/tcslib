<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radMatrix_proj_indep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of Row Projections

**Claim.** For a fixed vector $x$, the scalar projections of the scaled Rademacher rows are mutually independent.

**Proof.** The rows are mutually independent random vectors by the row independence fact (`radJointMeasure_rows_iid`). For each row, apply the measurable map sending a row $r$ to the scalar sum $\sum_j (r_j/\sqrt{k})x_j$. This map is measurable because it is a finite sum of coordinate maps multiplied by constants. Measurable functions applied separately to an independent family remain independent. The resulting scalar for row $i$ is the $i$th coordinate of the matrix image of $x$, which proves the claim.

**Key facts.** `radJointMeasure_rows_iid`.
