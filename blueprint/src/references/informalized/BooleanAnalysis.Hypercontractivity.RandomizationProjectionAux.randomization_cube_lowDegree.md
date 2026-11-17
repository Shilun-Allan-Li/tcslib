<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.randomization_cube_lowDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomization and low-degree projection

**Claim.** For each fixed outcome $x$, randomizing the product low-degree projection of $f$ through level $k$ gives the Boolean-cube Fourier–Walsh projection through level $k$ of the function $r\mapsto R_rf(x)$.

**Proof.** Fix a cube point $r$ and expand the low-degree projection as a sum over coordinate subsets $S$. The Fourier coefficient of the randomized function at $S$ is exactly the product component indexed by $S$ (`randomization_fourier_coefficient`). Meanwhile, taking the product component of the low-degree projection retains that component when $|S|\le k$ and gives zero otherwise (`component_lowDegree`). Substituting these two identities into the sums leaves, term by term, the same subset-indexed sum on both sides: each term is the character at $r$ times the component when $|S|\le k$, and zero when $|S|>k$. Hence the functions agree at every $r$, and therefore are equal.

**Key facts.** `BooleanAnalysis.Hypercontractivity.randomization_fourier_coefficient`, `BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.component_lowDegree`.
