<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean :: rows_indep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of matrix-vector coordinates

**Claim.** If the rows of a random matrix are mutually independent, then for each fixed vector $x$, the coordinates of its product with that matrix are mutually independent.

**Proof.** For each row, map its vector of entries $r$ to the scalar $\sum_j r_jx_j$. This map is measurable: it is a finite sum of coordinate evaluations multiplied by fixed constants. Applying this measurable map separately to each independent row preserves mutual independence. By the definition of matrix-vector multiplication, the resulting scalar for row $i$ is exactly the $i$th coordinate of $A(\omega)x$.
