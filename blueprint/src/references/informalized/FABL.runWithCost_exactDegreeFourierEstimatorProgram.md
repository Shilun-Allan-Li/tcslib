<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.runWithCost_exactDegreeFourierEstimatorProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree-bounded estimator law

**Claim.** For every target and degree bound, the law of the degree-bounded Fourier estimator program is the law obtained by drawing a matrix of independent uniform cube inputs, labeling each with the target, and applying the estimator’s output rule, with its specified cost.

**Proof.** By definition, the estimator program is a random-example-matrix-output program whose index set is the low-degree Fourier family, whose row length is the prescribed sample count, whose local-work charge is the displayed estimator cost, and whose output rule forms the hypothesis by rounding each empirical Fourier coefficient to the stated granularity. The run-with-cost definition for this program is exactly its random-example-matrix-output law. Thus the claimed equality follows by unfolding these definitions.
