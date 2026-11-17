<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.decisionTreeSizeClass_work_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision tree learner work bound

**Claim.** If a real-output decision tree computes the real-valued sign representation of the target and has at most $s$ leaves, then every supported outcome of the specified learner has local work at most the displayed polynomial in $n$, $s$, and $1/\varepsilon$.

**Proof.** The Fourier $1$-norm of the target is bounded by the tree's leaf count (`FABL.fourierOneNorm_le_leafCount_of_decisionTree`), hence by $s$. The norm is nonnegative (`FABL.fourierOneNorm_nonneg`), so these inequalities give the nonnegative norm hypothesis needed for the learner's work bound. Applying the work-cost theorem for targets with bounded Fourier $1$-norm (`FABL.fourierOneNormClass_work_polynomial_le`) yields the claimed estimate.

**Key facts.** `FABL.fourierOneNorm_le_leafCount_of_decisionTree`, `FABL.fourierOneNorm_nonneg`, `FABL.fourierOneNormClass_work_polynomial_le`.
