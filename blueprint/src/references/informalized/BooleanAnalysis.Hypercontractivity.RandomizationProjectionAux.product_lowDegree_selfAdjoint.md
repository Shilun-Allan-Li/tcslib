<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/ProjectionBounds.lean :: BooleanAnalysis.Hypercontractivity.RandomizationProjectionAux.product_lowDegree_selfAdjoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjointness of the low degree projection

**Claim.** For functions $f,g$ on the product space, the expectation of the low degree projection of $f$ times $g$ equals the expectation of $f$ times the low degree projection of $g$.

**Proof.** Expand each low degree projection as a sum over sets $S$ with $|S|\le k$, and expand each component into its alternating sum over subsets $T\subseteq S$. Expectation distributes over these finite sums (`BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum`), so it suffices to compare corresponding terms. Each term has a constant factor $(-1)^{|S|-|T|}$. The conditional expectation is self-adjoint (`BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint`): the expectation of the conditional expectation of $f$ times $g$ equals that of $f$ times the conditional expectation of $g$. Pulling the constant factor through expectation (`BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`) and rearranging scalar multiplication identifies the terms. Sets with $|S|>k$ contribute zero on both sides. Summing the equalities proves the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_sum`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.condExp_selfAdjoint`.
