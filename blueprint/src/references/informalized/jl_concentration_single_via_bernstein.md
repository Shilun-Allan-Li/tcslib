<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ConcentrationBound.lean :: jl_concentration_single_via_bernstein -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernstein Concentration for Row Squares

**Claim.** For independent measurable row projections whose centered squares satisfy a common Bernstein moment-generating-function bound, the probability that the squared norm of $Ax$ differs from $\|x\|^2$ by more than $s$ is at most $2\exp(-s^2/(4kc))$ whenever $0\le s\le2kc\,t_{\max}$.

**Proof.** Use the centered-squared independent-variable tail bound (`centered_squared_iid_tail`) on the coordinate functions $Y_i(\omega)=(A(\omega)x)_i$. It bounds the deviation of $\sum_iY_i^2$ from $k\sigma^2$ by the stated Bernstein tail, using the measurability, independence, and Bernstein hypotheses. Here the row centering parameter is $\sigma^2=\|x\|^2/k$. The Euclidean norm identity (`norm_sq_toEuclideanLin`) identifies $\|Ax\|^2$ with $\sum_iY_i^2$, and the finite index set has cardinality $k$, so $k\sigma^2=\|x\|^2$. Thus the event and exponent in the abstract bound become exactly those asserted.

**Key facts.** `centered_squared_iid_tail`, `norm_sq_toEuclideanLin`.
