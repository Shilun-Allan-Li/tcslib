<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.deterministicSmallBiasFourierEstimator_work_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic Work Bound

**Claim.** As the scale of small-bias Fourier estimation tasks tends to infinity, the estimator's work is $O((\text{scale}+1)^8)$.

**Proof.** The resource-bounds proposition (`deterministicSmallBiasFourierEstimatorCost_resource_bounds`) bounds the work of every task by its polynomial budget $2^{18}(\text{scale}+1)^8$. Casting to the reals preserves the inequality, and the quantities involved are nonnegative, so their norms are their values. Hence the work is bounded everywhere by the constant $2^{18}$ times $(\text{scale}+1)^8$. The bounded characterization of big-O gives the asserted asymptotic bound.

**Key facts.** `FABL.deterministicSmallBiasFourierEstimatorCost_resource_bounds`.
