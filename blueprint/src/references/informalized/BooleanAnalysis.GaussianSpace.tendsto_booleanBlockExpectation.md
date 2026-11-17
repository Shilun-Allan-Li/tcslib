<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.tendsto_booleanBlockExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convergence of Boolean Block Expectations

**Claim.** For $0\le\rho\le1$, the Boolean block expectations of every continuous complex-valued torus function converge to its integral under the correlated Gaussian law, after applying the Gaussian torus map.

**Proof.** Let the measure on the torus be the pushforward of the correlated Gaussian measure by the Gaussian pair torus map. Integration against this pushforward, viewed as a continuous linear functional on continuous functions, is the desired limiting integral; the identity follows from the change-of-variables formula (`compactIntegralCLM_apply`, together with continuity of the pair map `continuous_gaussianPairTorusMap`). The sequence of Boolean block expectations has operator norm at most one (`norm_booleanBlockExpectation_le`), matching the norm bound for integration against a probability measure. It therefore suffices to prove convergence on a dense spanning family of torus characters. The characters span a dense subspace of continuous functions (`UnitAddTorus.span_mFourier_closure_eq_top`). For each character, its value after the Gaussian pair map is an exponential whose frequency is determined by the character (`mFourier_gaussianPairTorusMap`); the convergence of the corresponding Boolean weighted sums to the correlated Gaussian integral is exactly the character-level convergence result (`tendsto_sum_noiseKernel_normalizedCubeBlocks_phase`). Uniform boundedness and density then extend convergence from this spanning family to every continuous function (`tendsto_clm_of_dense_span`).

**Key facts.** `BooleanAnalysis.GaussianSpace.compactIntegralCLM_apply`, `BooleanAnalysis.GaussianSpace.continuous_gaussianPairTorusMap`, `BooleanAnalysis.GaussianSpace.norm_booleanBlockExpectation_le`, `BooleanAnalysis.GaussianSpace.tendsto_clm_of_dense_span`, `BooleanAnalysis.GaussianSpace.mFourier_gaussianPairTorusMap`, `BooleanAnalysis.GaussianSpace.tendsto_sum_noiseKernel_normalizedCubeBlocks_phase`.
