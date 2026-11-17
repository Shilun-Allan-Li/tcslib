<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.deterministicSmallBiasFourierEstimatorCost_queries -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator query count

**Claim.** The deterministic small-bias Fourier estimator uses a number of membership queries equal to the input's sample count.

**Proof.** The estimator cost is the sum of a construction cost with query component zero and the small-bias Fourier estimator cost. The latter is the sum of a query-batch cost, whose query component is the sample count, and a work-only term with query component zero. Adding these components leaves precisely the sample count.
