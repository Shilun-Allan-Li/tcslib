<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: measurable_radMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the scaled matrix map

**Claim.** The map sending each real array to the matrix with entries divided by $\sqrt{k}$ is measurable for the product measurable structures.

**Proof.** A map into a function space with the product measurable structure is measurable when each coordinate map is measurable. Fix a row index $i$ and column index $j$. The coordinate $\omega\mapsto\omega_{ij}$ is obtained by evaluating first at $i$ and then at $j$, so it is measurable. Dividing this real-valued measurable function by the fixed constant $\sqrt{k}$ preserves measurability. Thus every matrix coordinate is measurable, and hence the matrix-valued map is measurable.
