<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.UniformRefinement.paddedCloneFailure_le_tupleFailure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded-clone failure bound

**Claim.** For each padded clone occurrence, the indicator that its padded clone scope is not injective is at most the indicator that its clone-index tuple is not injective.

**Proof.** If the clone-index tuple is injective, equality of two padded clone scope values forces equality of their second coordinates, hence equality of the corresponding clone indices. Injectivity of the tuple then gives equality of the positions after casting into the padded range; the arity bound makes that cast injective, so the positions are equal. Thus the padded clone scope is injective whenever the clone-index tuple is injective, which proves the indicator inequality in this case. If the tuple is not injective, its failure indicator is $1$, and the padded-scope failure indicator is either $0$ or $1$, so the inequality also holds.
