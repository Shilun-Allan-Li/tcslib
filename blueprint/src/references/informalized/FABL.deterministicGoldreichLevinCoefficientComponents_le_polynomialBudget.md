<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.deterministicGoldreichLevinCoefficientComponents_le_polynomialBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient Components Fit the Polynomial Budget

**Claim.** The small-bias construction work, sample count, and local Fourier-estimation work are each at most the coefficient input's polynomial budget.

**Proof.** Use the resource bounds for the deterministic small-bias Fourier estimator on the full set $U$ of coordinates. Its query count is the sample count, by `deterministicSmallBiasFourierEstimatorCost_queries`; its work is the sum of the small-bias construction work, sample count, and local estimator work, by `deterministicSmallBiasFourierEstimatorCost_work`. The resource theorem `deterministicSmallBiasFourierEstimatorCost_resource_bounds` bounds both query count and total work by the polynomial budget. Thus the sample count is within budget, and since the total work is a sum of nonnegative terms, each of the other two work quantities is within budget as well.

**Key facts.** `FABL.deterministicSmallBiasFourierEstimatorCost_resource_bounds`, `FABL.deterministicSmallBiasFourierEstimatorCost_queries`, `FABL.deterministicSmallBiasFourierEstimatorCost_work`.
