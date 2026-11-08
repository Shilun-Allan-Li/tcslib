<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.influence_eq_sum_components -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Decomposition

**Claim.** The influence at coordinate $i$ is the sum of the expected squared components over all coordinate sets containing $i$.

**Proof.** By Parseval's identity (`parseval`), the expected square of the discrete Laplacian at coordinate $i$ is the sum, over all sets $S$, of the expected squares of its $S$-components. The component of the Laplacian is the component of $f$ when $i\in S$, and vanishes otherwise (`component_laplacian`). Substituting this description into Parseval's sum gives exactly the claimed decomposition; the expectation of a constant is evaluated using `expect_const` in the bookkeeping of the zero cases.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_laplacian`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
