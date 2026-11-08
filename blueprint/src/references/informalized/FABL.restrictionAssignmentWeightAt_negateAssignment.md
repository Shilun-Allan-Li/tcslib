<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictionAssignmentWeightAt_negateAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negation invariance of assignment weight

**Claim.** Exchanging the two fixed states in every coordinate, while leaving free states unchanged, preserves the assignment weight for every real parameter.

**Proof.** At each coordinate, negation leaves a free state free and exchanges the two fixed states. The coordinate weight depends only on whether the state is free or fixed: it is $\delta$ in the first case and $(1-\delta)/2$ in the second. Thus negation preserves every coordinate factor, and so preserves their product.
