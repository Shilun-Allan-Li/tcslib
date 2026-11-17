<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.rationalRestrictedFourierWeightEstimateFromOracle_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle restricted estimate cast

**Claim.** The rational restricted weight estimate obtained by querying the target, viewed as real, equals the real restricted Fourier weight estimate.

**Proof.** First apply the rational-to-real identity for estimates from answers (`rationalRestrictedFourierWeightEstimateFromAnswers_cast`), reducing the claim to the real estimate formed from the oracle answers. Reindex its combined query by the corresponding outer and inner sample pair. For each outer sample, the oracle query point is the combination of that sample's fixed assignment and the inner sample's free assignment. The inner sum is therefore the restricted Fourier coefficient observation at that fixed assignment; squaring it and averaging over outer samples gives exactly the restricted Fourier weight estimate.

**Key facts.** `FABL.rationalRestrictedFourierWeightEstimateFromAnswers_cast`.
