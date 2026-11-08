<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyFourierEstimatorOutput_decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator encoding round trip

**Claim.** Decoding the encoding of the Fourier estimator output formed from the chosen inputs returns that same output.

**Proof.** Apply the general encode–decode identity for sparse Fourier hypotheses to the estimator output itself. It says that decoding the encoding of any hypothesis returns that hypothesis, so the decoded value is exactly the original estimator output.

**Key facts.** `FABL.SparseFourierHypothesis.decode_encode`.
