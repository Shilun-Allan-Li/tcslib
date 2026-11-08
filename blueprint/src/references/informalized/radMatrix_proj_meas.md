<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radMatrix_proj_meas -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of a Row Projection

**Claim.** For fixed $x$ and row index $i$, the map taking an array to the $i$th coordinate of its scaled matrix image of $x$ is measurable.

**Proof.** The coordinate of the matrix image is the finite sum over columns of the matrix entry in row $i$ times the fixed coordinate $x_j$. Each matrix entry is the corresponding array coordinate divided by the constant $\sqrt{k}$, hence is measurable; multiplying by $x_j$ preserves measurability. A finite sum of measurable real-valued functions is measurable, giving the result.
