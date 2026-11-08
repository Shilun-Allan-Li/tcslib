<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.randomization_cube_noise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomization commutes with noise

**Claim.** For each fixed outcome $x$, randomizing the product noise transform of $f$ gives the Boolean-cube noise transform, with parameter $\rho$, of the randomized function $r\mapsto R_rf(x)$.

**Proof.** Fix a cube point $r$ and expand the Boolean-cube noise transform in its subset-indexed Fourier sum. The Fourier coefficient of $r\mapsto R_rf(x)$ at $S$ equals the product component indexed by $S$ (`randomization_fourier_coefficient`). In the other expression, the component of the product noise transform at $S$ is $\rho^{|S|}$ times the original component (`component_noise`). Substituting these identities makes the two sums identical term by term: each subset contributes its character at $r$, multiplied by $\rho^{|S|}$ and the same product component. Thus the functions agree at every cube point.

**Key facts.** `BooleanAnalysis.Hypercontractivity.randomization_fourier_coefficient`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`.
