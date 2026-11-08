<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/NoiseKernel.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_kernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Kernel formula for conditional expectation

**Claim.** For a product of finite probability spaces, conditional expectation on a coordinate subset is a sum over outcomes with a product kernel: each selected coordinate contributes the equality indicator, and each other coordinate contributes its probability weight.

**Proof.** For any fixed outcome $a$, the product of coordinate equality indicators selects exactly the term $y=a$ in the sum over outcomes. Insert this identity into the defining expectation of the function evaluated with coordinates in $S$ fixed at $x$. Interchange the two finite sums, collecting for each $y$ the total mass of samples whose mixed outcome agrees with $y$. This mass factors coordinatewise. On coordinates in $S$, agreement requires $x_i=y_i$, giving the equality indicator; on coordinates outside $S$, summing the coordinate weights over the allowed value gives the weight of $y_i$. The coordinate weights sum to one, so the fixed coordinates contribute precisely their indicators. Substituting these factors yields the claimed kernel formula.
