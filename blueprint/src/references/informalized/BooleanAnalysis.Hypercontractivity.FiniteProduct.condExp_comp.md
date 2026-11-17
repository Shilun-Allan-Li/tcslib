<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of conditional expectations

**Claim.** For subsets $S,T$ of the coordinates, applying conditional expectation over the coordinates outside $T$ and then over those outside $S$ gives conditional expectation over the coordinates outside $S\cap T$.

**Proof.** Expand the two conditional expectations using their definitions. The nested expectations average over two independently sampled outcomes: the resulting argument of $f$ uses $x$ on $S\cap T$, the first sample on $T\setminus S$, and the second sample on the remaining coordinates. The product measure permits swapping these samples on the coordinates in $T\setminus S$; the expectation-swap identity ( `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_swap_samples` ) therefore rewrites the nested average as one in which the first sample supplies every coordinate outside $S\cap T$. The inner expectation is then constant in its sample, so the fact that expectation preserves constants ( `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const` ) reduces the expression to the conditional expectation over $S\cap T$, as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_swap_samples`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const`.
