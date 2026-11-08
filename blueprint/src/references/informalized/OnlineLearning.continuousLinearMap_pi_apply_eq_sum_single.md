<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/ConvexMinimaxSeparation.lean :: OnlineLearning.continuousLinearMap_pi_apply_eq_sum_single -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Expansion of a Linear Functional

**Claim.** Every continuous linear functional on $\mathbb{R}^{\iota}$, for finite $\iota$, satisfies $L(z)=\sum_{i\in\iota}z_iL(e_i)$, where $e_i$ is the $i$th standard basis vector.

**Proof.** Decompose $z$ as the finite sum of its coordinate-supported vectors, each supported at one index. Linearity of $L$ turns its value on this sum into the sum of its values on those vectors. The vector supported at $i$ with value $z_i$ is $z_i e_i$, so linearity makes its image $z_iL(e_i)$. Summing these terms gives the formula.
