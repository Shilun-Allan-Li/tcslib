<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.runWithCost_zeroDimensionExactSparseSpectrumLearner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of the Zero-Dimensional Sparse-Spectrum Learner

**Claim.** The learner queries the target once at the all-one input, returns the constant sparse Fourier hypothesis with that target value, and has cost $(0,1,1)$.

**Proof.** Unfold the learner and its run. Its single query batch has size one and contains the all-one input, so the sole answer is the target value there. The program returns the constant sparse Fourier hypothesis formed from that answer. The query-batch cost for one query is $(0,1,1)$, giving the stated output and cost directly.
