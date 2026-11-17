<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.ProductAux.noise_norm_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise contracts the quadratic norm

**Claim.** For a finite product space, noise with parameter between $0$ and $1$ does not increase the quadratic norm of any function.

**Proof.** Apply the product noise contraction theorem (`product_noise_norm_two_le`) to the given product space, parameter, and function. Its hypotheses are precisely that the parameter is nonnegative and at most one, and its conclusion is the stated norm inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_noise_norm_two_le`.
