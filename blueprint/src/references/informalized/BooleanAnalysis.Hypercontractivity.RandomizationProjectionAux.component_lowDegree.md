<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.component_lowDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Components of a low degree projection

**Claim.** For every set $S$, the $S$-component of the low degree projection equals the original $S$-component when $|S|\le k$, and is zero otherwise.

**Proof.** Write the low degree projection as the finite sum over sets $T$ of the component of $f$ on $T$, multiplied by the indicator of $|T|\le k$. By linearity of expectation and of the finite alternating sum defining a component, its $S$-component is the corresponding sum over $T$ of those coefficients times the $S$-component of the $T$-component of $f$. The component-composition identity (`BooleanAnalysis.Hypercontractivity.RandomizationAux.component_component`) says this inner component is the original $S$-component if $S=T$, and zero otherwise. Thus only the term $T=S$ survives, giving the original component when $|S|\le k$ and zero when $|S|>k$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_component`.
