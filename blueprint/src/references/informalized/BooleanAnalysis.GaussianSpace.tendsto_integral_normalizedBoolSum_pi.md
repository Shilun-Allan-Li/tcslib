<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/NormalizedBlocks.lean :: BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolSum_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product convergence for normalized sum laws

**Claim.** For every bounded continuous function on $\mathbb R^n$, its integral against the product of the normalized Boolean sum laws converges to its integral against product standard Gaussian measure.

**Proof.** Regard standard Gaussian measure as a probability measure. The scalar convergence hypothesis needed for the product theorem is supplied by the convergence of normalized Boolean-sum expectations to Gaussian expectations for every Lipschitz test function (tendsto_integral_normalizedBoolSum). Apply the product convergence theorem (tendsto_integral_pi_of_scalar_lipschitz) to these one-dimensional laws and the bounded continuous function on $\mathbb R^n$. Its conclusion is exactly the claimed convergence of product integrals.

**Key facts.** `BooleanAnalysis.GaussianSpace.tendsto_integral_normalizedBoolSum`, `BooleanAnalysis.GaussianSpace.tendsto_integral_pi_of_scalar_lipschitz`.
