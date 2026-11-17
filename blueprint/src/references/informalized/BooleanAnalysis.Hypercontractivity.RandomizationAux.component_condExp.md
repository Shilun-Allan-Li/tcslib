<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.component_condExp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Components after conditional expectation

**Claim.** The $S$-component of the conditional expectation of $f$ given coordinates in $J$ equals the $S$-component of $f$ when $S\subseteq J$, and is zero otherwise.

**Proof.** Expand the $S$-component as a finite alternating sum and move that sum through expectation, using linearity of expectation over finite sums (`FiniteProduct.expect_sum_mul`). The composition rule for conditional expectations says that conditioning successively on coordinate sets replaces them by their intersection (`FiniteProduct.condExp_comp`). After interchanging the sets in the intersection, the expression becomes the conditional expectation given $J$ of the $S$-component of $f$. The conditional-expectation rule for a component (`condExp_component`) says this equals the original component precisely when $S\subseteq J$, and is zero otherwise.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_comp`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_component`.
