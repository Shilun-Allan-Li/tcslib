<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfExpectation_mul_sq_le_sq_mul_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cauchy–Schwarz for expectations

**Claim.** For real-valued functions $f$ and $g$ on a finite probability space, $\bigl(\mathbb{E}_p[fg]\bigr)^2\le \mathbb{E}_p[f^2]\,\mathbb{E}_p[g^2]$.

**Proof.** Apply the finite-sum Cauchy–Schwarz inequality to the vectors with coordinates $\sqrt{(p(x)).\mathrm{toReal}}f(x)$ and $\sqrt{(p(x)).\mathrm{toReal}}g(x)$. Their inner product is $\sum_x (p(x)).\mathrm{toReal}f(x)g(x)$, because the square of the square root is the probability weight. The squared norm of the first vector is $\sum_x (p(x)).\mathrm{toReal}f(x)^2$, and the second has the analogous expression. These are exactly the three expectations in the desired inequality, so Cauchy–Schwarz gives the result.
