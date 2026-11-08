<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependence.lean :: FABL.matrixColumnSum_f₂Support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Action from Support

**Claim.** For an $m\times n$ matrix $H$ over $\mathbb F_2$ and $\gamma\in\mathbb F_2^n$, the sum of the columns of $H$ indexed by the support of $\gamma$ equals $H\gamma$.

**Proof.** The support-to-indicator-vector correspondence says that the indicator vector of the support of $\gamma$ is exactly $\gamma$: in each coordinate, membership in the support means the coordinate is nonzero, and the only nonzero element of $\mathbb F_2$ is $1$. Replacing the indicator vector in the matrix-vector product defining the column sum by $\gamma$ yields $H\gamma$, as required.
