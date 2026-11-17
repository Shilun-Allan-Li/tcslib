<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianBoundary_eq_density -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Boundary as Density

**Claim.** For every $q\in\mathbb{N}$, the Gaussian boundary associated with $q$ equals the standard Gaussian density at the upper quantile corresponding to mass $1/(q+2)$.

**Proof.** The Gaussian mass associated with $q$ lies strictly between $0$ and $1$. The Gaussian isoperimetric function at any such mass is the standard Gaussian density evaluated at the upper quantile of that mass (`gaussianIsoperimetric_apply_of_mem_Ioo`). Apply this identity to the mass associated with $q$; by definition, its upper quantile is the threshold for $q$. The resulting equality is the claimed formula for the Gaussian boundary.

**Key facts.** `FABL.gaussianIsoperimetric_apply_of_mem_Ioo`.
