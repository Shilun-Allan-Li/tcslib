<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanAnalysis.influence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of influence

**Claim.** The influence of every coordinate on a real-valued function on the Boolean cube is nonnegative.

**Proof.** The influence is the uniform expectation of $(f(x)-f(x^i))^2/4$. Each integrand is nonnegative because it is a square divided by a positive number. The uniform weight is positive, so the finite weighted sum defining the expectation is nonnegative as well.
