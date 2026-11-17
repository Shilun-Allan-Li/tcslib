<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.restrictedWeightFreeSample_isBiased -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias of the Free-Coordinate Projection

**Claim.** The projected sample on coordinates in $J$ has every nonzero Fourier coefficient bounded in absolute value by $\varepsilon/(4s)$.

**Proof.** The inner sample has bias bound $\varepsilon/(4s)$, since its input parameter satisfies `innerInput_biasParameter` and the general sample guarantee is `sample_isBiased`. Express the desired bias assertion as bounds on expectations of nonzero Walsh characters using `isBiased_iff_expectation`. Given a nonzero frequency on the projected coordinates, lift it to a nonzero ambient frequency (`coordinateFrequencyLift_ne_zero`). The Walsh character at the projected sample equals the ambient Walsh character at the lifted frequency (`vectorWalshCharacter_coordinateProjection`). The expectation of a character under the uniform pushforward distribution equals its expectation over sample indices (`expectation_uniformPushforward`), so the projected expectation is precisely the ambient one at the lifted frequency, which has the stated bound.

**Key facts.** `FABL.RestrictedWeightInput.innerInput_biasParameter`, `FABL.SmallBiasFourierInput.sample_isBiased`, `FABL.ProbabilityDensity.isBiased_iff_expectation`, `FABL.coordinateFrequencyLift_ne_zero`, `FABL.ProbabilityDensity.expectation_uniformPushforward`, `FABL.vectorWalshCharacter_coordinateProjection`.
