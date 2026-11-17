<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.productNormComparisonConstant_tendsto_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison Constant Limit

**Claim.** As $\lambda$ approaches $1/2$ through values with $0<\lambda<1/2$, the comparison constant $C(\lambda)$ tends to $e$.

**Proof.** This is exactly the limit established by the auxiliary result `ComparisonAux.constant_tendsto_half`: the piecewise-defined comparison constant converges to $e$ along the specified one-sided neighborhood of $1/2$. The theorem follows by applying that result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ComparisonAux.constant_tendsto_half`.
