<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Basic.lean :: BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Constant

**Claim.** The product expectation of the constant function with value $c$ is $c$.

**Proof.** By definition, the expectation is $\sum_x m(x)c$. Factor out the constant to obtain $c\sum_x m(x)$. The product masses sum to $1$ (`mass_sum`), so this equals $c$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.mass_sum`.
