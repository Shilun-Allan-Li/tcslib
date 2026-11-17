<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/NoiseKernel.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.component_kernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kernel formula for product components

**Claim.** For a product of finite probability spaces, each component of a function is the sum over outcomes of the function times a product kernel whose coordinate factor is the difference between the equality indicator and the coordinate weight on the selected coordinates, and the weight on the other coordinates.

**Proof.** Expand the component as the alternating sum of conditional expectations over subsets of $S$. For each such subset, the conditional expectation kernel formula ( `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_kernel` ) expresses that expectation as a sum over outcomes, with equality indicators on the coordinates conditioned on and probability weights elsewhere. Distribute the alternating coefficient through these finite sums, then interchange the subset and outcome sums. For each fixed outcome, the signed sum over subsets of $S$ factors coordinatewise: the signed product-kernel identity ( `BooleanAnalysis.Hypercontractivity.FiniteProduct.signed_product_kernel` ) says this is the product of the differences between the equality indicator and weight on coordinates in $S$, and the weight on coordinates outside $S$. Multiplying by the function value and summing over outcomes gives the formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_kernel`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.signed_product_kernel`.
