<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.correlationQuadraticForm_euclideanCorrelationCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic form in Euclidean coordinates

**Claim.** For every real number $\rho$ and every vector $t=(t_0,t_1)\in\mathbb{R}^2$, the quadratic form $t_0^2+2\rho t_0t_1+t_1^2$ equals $t^{\mathsf T}\begin{pmatrix}1&\rho\\\rho&1\end{pmatrix}t$.

**Proof.** In Euclidean coordinates, the vector has entries $t_0,t_1$. Multiplying by the displayed matrix gives $(t_0+\rho t_1,\rho t_0+t_1)$. Taking the dot product with $t$ yields $t_0(t_0+\rho t_1)+t_1(\rho t_0+t_1)$, which expands to $t_0^2+2\rho t_0t_1+t_1^2$.
