<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.runWithCost_restrictedFourierWeightEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator Run Cost and Output

**Claim.** The restricted Fourier weight estimator's run law is the successive uniform sampling of its three input sequences, followed by its specified estimate and fixed estimator cost.

**Proof.** Unfold the estimator program and apply the established run calculation for the observation batch followed by its empirical finishing step (`runWithCost_restrictedFourierWeightObservationBatchProgramWith_empirical`). This leaves three successive uniform input laws, each binding to the deterministic estimate computed from those inputs and the target, paired with the resulting cost. The three uniform batches each contribute $mn$ units of work; the observation stage contributes $m(2+\mathrm{work}(J,S))$ and the finishing step contributes $m+1$. Thus the work total is $3mn+m(2+\mathrm{work}(J,S))+(m+1)$, while the query count is $2m$ and the random-example count is zero. This is the stated estimator cost.

**Key facts.** `FABL.runWithCost_restrictedFourierWeightObservationBatchProgramWith_empirical`.
