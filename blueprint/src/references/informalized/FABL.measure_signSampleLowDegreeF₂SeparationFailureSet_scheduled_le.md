<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.measure_signSampleLowDegreeF₂SeparationFailureSet_scheduled_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scheduled Low Degree Separation

**Claim.** For the scheduled sample count, the probability that evaluation fails to separate the low degree $\mathbb F_2$ coefficient vectors is at most $\delta$.

**Proof.** Let $m$ be the scheduled sample count and map each sign-cube sample to its corresponding binary-cube sample by the coordinatewise equivalence. This bijection sends the uniform distribution on sign-cube sample sequences to the uniform distribution on binary-cube sample sequences (\texttt{map\_uniformPMF\_equiv}). The sign-side failure event is exactly the preimage of the binary-side failure event by definition. The measure of a preimage under the mapped distribution equals the measure of the original event under that distribution. Consequently, the sign-side failure probability equals the binary-side failure probability, which is at most $\delta$ by the scheduled binary separation bound (\texttt{measure\_lowDegreeF₂SeparationFailureSet\_scheduled\_le}).

**Key facts.** `FABL.map_uniformPMF_equiv`, `FABL.measure_lowDegreeF₂SeparationFailureSet_scheduled_le`.
