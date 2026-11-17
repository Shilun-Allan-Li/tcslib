<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.separating_weight_sum_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Total Separator Weight

**Claim.** Under strict separation from the nonempty upper image, the sum of the negated coordinate values of the functional is strictly positive.

**Proof.** The coordinate nonpositivity result (`separating_coordinate_nonpos`) says that every coordinate value $L(e_y)$ is nonpositive, so each term $-L(e_y)$ in the sum is nonnegative. At least one coordinate value must be nonzero: otherwise the coordinate expansion of a functional on a finite product (`continuousLinearMap_pi_apply_eq_sum_single`) would imply $L=0$, contrary to the result that a separating functional is nonzero (`separating_functional_ne_zero`). That nonzero coordinate value, being nonpositive, is strictly negative. Its negation is positive, so the sum of all the nonnegative terms, one of which is positive, is strictly positive.

**Key facts.** `OnlineLearning.separating_coordinate_nonpos`, `OnlineLearning.separating_functional_ne_zero`, `OnlineLearning.continuousLinearMap_pi_apply_eq_sum_single`.
