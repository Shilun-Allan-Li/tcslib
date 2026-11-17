<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.extendedFunctional_noise_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noisy Functional as a Symmetric Pair

**Claim.** The extended functional of the noisy inputs equals the uniform expectation of the pair length with interpolation parameter $\rho$ and clock $(\rho T_\rho d_f(x))^2$, using the stated average and difference inputs and length vectors.

**Proof.** Rewrite the expectation over the $(n+1)$-dimensional cube as the average over the two choices of the last bit (`expect_succ_eq_iterated`). On each slice, the sum of squared derivatives and additional coordinates splits into the square of the last-coordinate difference plus the squared length of the restricted vector (`extended_length_snoc`). The last-coordinate derivative of the noisy function is $\rho$ times the noise of its difference, by the derivative identities for a slice and for the noise operator (`derivative_last_snoc`, `derivative_last_noise_snoc`). The restricted noisy vectors are the noisy average vectors plus or minus $\rho$ times the noisy difference vectors (`lengthVector_restrictLast_noiseOp`); the restriction formula for the noisy function gives the corresponding scalar terms (`restrictLast_noiseOp_eq`). Substituting the signs of the false and true bits (`boolToSign_false`, `boolToSign_true`) into the two square roots yields exactly the two terms in the pair length with parameter $\rho$ and the stated clock. Averaging over the slices and then over $x$ proves the identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_succ_eq_iterated`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.extended_length_snoc`, `BooleanAnalysis.GaussianSpace.derivative_last_snoc`, `BooleanAnalysis.GaussianSpace.derivative_last_noise_snoc`, `BooleanAnalysis.GaussianSpace.BobkovInterpolation.lengthVector_restrictLast_noiseOp`, `BooleanAnalysis.GaussianSpace.restrictLast_noiseOp_eq`, `BooleanAnalysis.boolToSign_false`, `BooleanAnalysis.boolToSign_true`.
