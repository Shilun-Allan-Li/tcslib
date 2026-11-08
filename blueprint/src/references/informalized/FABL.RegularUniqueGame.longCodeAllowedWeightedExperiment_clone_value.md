<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCodeAllowedWeightedExperiment_clone_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction preserves cloned value

**Claim.** The value of the cloned long-code experiment restricted to predicates in $\Psi$ equals the value of the unrestricted cloned experiment.

**Proof.** Apply the clone-value formula (\texttt{FABL.WeightedConstraintExperiment.clone\_value\_eq\_iterated}) to each experiment. Both values are then expectations over the same long-code experiment law, followed by an average over clone choices. For each outcome and clone choice, the restricted experiment uses the tester predicate together with its proof of membership in $\Psi$; the template evaluation forgets that membership proof and evaluates the same predicate on the same assigned values. Thus the two payoffs agree pointwise, so their expectations agree.

**Key facts.** `FABL.WeightedConstraintExperiment.clone_value_eq_iterated`.
