<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/ContinuousBounds.lean :: BooleanAnalysis.GaussianSpace.gaussian_two_function_continuous -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuous Gaussian two-function inequality

**Claim.** Under the stated conditions on $r,s,\rho$, the correlated Gaussian expectation of the product of the absolute values of two continuous torus functions is bounded by the product of their respective Gaussian $L^{1+r}$ and $L^{1+s}$ norms.

**Proof.** For each block dimension $m$, apply the positive-offset two-function inequality on the Boolean cube to the functions obtained by evaluating $F$ and $G$ on the normalized blocks. The identity expressing the Boolean noise-operator inner product as a weighted sum (`innerProduct_noiseOp_eq_weighted_sum`) identifies that bound with the corresponding finite double sum. The noise kernel has total mass one in each variable (`noiseKernel_sum_left`, `noiseKernel_sum_right`), which also makes the separate finite sums for the two marginal moments agree with the Boolean expectations. Now let $m$ tend to infinity. The Boolean block expectation convergence theorem (`tendsto_booleanBlockExpectation_real`) gives convergence of the double sums to the correlated Gaussian expectation for the product function, and separately gives convergence of each marginal moment to its Gaussian integral. Taking the continuous powers $1/(1+r)$ and $1/(1+s)$ in these limits preserves the bounds. Passing the finite-dimensional inequalities to the limit yields the asserted inequality.

**Key facts.** `BooleanAnalysis.GaussianSpace.boolean_two_function_positiveOffsets`, `BooleanAnalysis.Hypercontractivity.innerProduct_noiseOp_eq_weighted_sum`, `BooleanAnalysis.Hypercontractivity.noiseKernel_sum_left`, `BooleanAnalysis.Hypercontractivity.noiseKernel_sum_right`, `BooleanAnalysis.GaussianSpace.tendsto_booleanBlockExpectation_real`.
