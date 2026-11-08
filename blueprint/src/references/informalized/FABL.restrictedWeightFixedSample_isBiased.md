<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.restrictedWeightFixedSample_isBiased -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias of the Fixed-Coordinate Projection

**Claim.** The projected sample on coordinates outside $J$ has every nonzero Fourier coefficient bounded in absolute value by $\varepsilon/(4s^2)$.

**Proof.** The outer sample has the required bias bound: its bias parameter and Fourier bound combine to give $\varepsilon/(4s^2)$ (`outerInput_biasParameter` and `sample_isBiased`). Recast bias as a bound on the expectation of each nontrivial Walsh character (`isBiased_iff_expectation`). For a nonzero frequency on the coordinates outside $J$, lift it to a frequency on all coordinates; the lift remains nonzero (`fixedCoordinateFrequencyLift_ne_zero`). The Walsh character of the lifted frequency on a full sample agrees with the original character evaluated on the projected sample (`vectorWalshCharacter_fixedCoordinateProjection`). Finally, expectation under the uniform pushforward sample is the same as expectation over its sample indices (`expectation_uniformPushforward`). Therefore the desired projected coefficient is exactly the ambient coefficient at the lifted nonzero frequency, and inherits the bound.

**Key facts.** `FABL.RestrictedWeightInput.outerInput_biasParameter`, `FABL.SmallBiasFourierInput.sample_isBiased`, `FABL.ProbabilityDensity.isBiased_iff_expectation`, `FABL.fixedCoordinateFrequencyLift_ne_zero`, `FABL.ProbabilityDensity.expectation_uniformPushforward`, `FABL.vectorWalshCharacter_fixedCoordinateProjection`.
