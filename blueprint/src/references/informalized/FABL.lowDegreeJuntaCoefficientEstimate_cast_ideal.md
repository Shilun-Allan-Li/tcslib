<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaCoefficientEstimate_cast_ideal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ideal Coefficient Estimate Under Reindexing

**Claim.** For any frequency in the stated family, the real value of the empirical rational Fourier coefficient from the batch labeled by the restricted function equals the empirical real Fourier coefficient of the reindexed restricted function on the corresponding reindexed inputs.

**Proof.** First, the ideal-sample identity (\(\texttt{FABL.lowDegreeJuntaCoefficientSamples_ideal}\)) identifies each reindexed labeled sample with the pair consisting of its reindexed input and the reindexed restricted function's value at that input. Thus the rational empirical coefficient is computed from samples labeled by that function. The real-cast identity for empirical Fourier coefficients (\(\texttt{FABL.empiricalFourierCoeff_cast}\)) then says that the real cast of this rational average equals the real empirical Fourier coefficient on those inputs.

**Key facts.** `FABL.lowDegreeJuntaCoefficientSamples_ideal`, `FABL.empiricalFourierCoeff_cast`.
