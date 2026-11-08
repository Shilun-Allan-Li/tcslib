<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: norm_sq_div_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared norm coordinate formula

**Claim.** For every natural number $k$ and vector $x\in\mathbb{R}^d$ with its Euclidean norm, $\|x\|^2/k=\sum_{j\in\mathrm{Fin}\,d}x_j^2/k$.

**Proof.** The Euclidean norm is the square root of the sum of the squared absolute values of the coordinates. Squaring this expression cancels the square root, since the sum is nonnegative. For each real coordinate, $|x_j|^2=x_j^2$. Finally, distributing division by $k$ across the finite sum gives the stated identity.
