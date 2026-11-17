<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.abs_restrictedFourierWeightOuterMean_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer Mean Approximation of Restricted Fourier Weight

**Claim.** The outer mean of the squared restricted Fourier coefficient differs from the restricted Fourier weight by at most $\varepsilon/4$.

**Proof.** Apply the restricted Fourier weight comparison theorem to the distribution on complementary-coordinate assignments obtained by pushing the uniform sample forward through the fixed-coordinate projection. The sample-bias result supplies its required bias bound, with parameter $s$ equal to the Fourier norm bound; the input hypotheses give $s\ge1$ and positive $\varepsilon$. That comparison theorem bounds the difference between the distributional expectation of the squared restricted coefficient and its uniform mean by $\varepsilon/4$. The pushforward expectation identity identifies the distributional expectation with the stated outer mean, while the reindexing identity identifies the uniform mean with the restricted Fourier weight. These identifications give the desired inequality.

**Key facts.** `FABL.restrictedWeightFixedSample_isBiased`, `FABL.SmallBiasInput.epsilon_pos`, `FABL.restrictionFourierWeight_equation6_7`, `FABL.ProbabilityDensity.expectation_uniformPushforward`, `FABL.restrictedFourierWeight_eq_mean_fixedReindex`.
