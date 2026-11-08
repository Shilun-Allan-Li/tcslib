<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityGaussianBoundary_isEquivalent_main -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Gaussian Boundary Equivalence

**Claim.** As $q\to\infty$ through the natural numbers, the Gaussian boundary associated with $q$ is asymptotically equivalent to $\frac{1}{q+2}\sqrt{2\log(q+2)}$.

**Proof.** The Gaussian isoperimetric profile, as its mass $\alpha$ tends to zero, is asymptotic to $\alpha\sqrt{2\log(1/\alpha)}$ (`gaussianIsoperimetric_isEquivalent_atBot`). The masses associated with $q$ tend to zero as $q$ tends to infinity (`tendsto_fknOptimalityGaussianMass_atBot`). Composing the profile equivalence with this convergence gives an asymptotic equivalence for the boundary along those masses. Since the mass is $1/(q+2)$, the comparison term becomes $\frac{1}{q+2}\sqrt{2\log(q+2)}$, as asserted.

**Key facts.** `FABL.gaussianIsoperimetric_isEquivalent_atBot`, `FABL.tendsto_fknOptimalityGaussianMass_atBot`.
