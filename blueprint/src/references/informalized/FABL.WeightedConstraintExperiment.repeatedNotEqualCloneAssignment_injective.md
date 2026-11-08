<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.repeatedNotEqualCloneAssignment_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Clone Assignment

**Claim.** The map sending clone $0$ to $-1$ and clone $1$ to $1$ is injective.

**Proof.** Take two clones with the same assigned sign. There are only two possibilities for each clone. If they are equal, the desired conclusion already holds; if they differ, one is clone $0$ and the other clone $1$, whose assigned signs are $-1$ and $1$, so their signs cannot be equal. Hence equal assigned signs force the clones to be equal.
