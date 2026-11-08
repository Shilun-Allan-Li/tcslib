<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_learningConsequencesTargetFamily_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning Target Family Size Bound

**Claim.** Under the stated total-influence bound, the learning-consequences target family has cardinality at most the learning-consequences family bound determined by $t$ and $\varepsilon$.

**Proof.** Write $J$ for the influential coordinates of the target at the prescribed threshold, and $k$ for the prescribed learning-consequences degree. The target family consists of subsets of $J$ of size at most $k$. The bound for low-degree subsets (`FABL.card_lowDegreeSubsets_le`) gives its cardinality at most $(k+1)(|J|+1)^k$. The influence hypothesis bounds $|J|$ by the prescribed coordinate cap (`FABL.card_influentialCoordinates_learningConsequencesThreshold_le`). Since raising nonnegative integers to the $k$th power and multiplying by $k+1$ preserve order, replacing $|J|$ by that cap yields the claimed family bound, which is exactly $(k+1)$ times one more than the cap raised to $k$.

**Key facts.** `FABL.card_lowDegreeSubsets_le`, `FABL.card_influentialCoordinates_learningConsequencesThreshold_le`.
