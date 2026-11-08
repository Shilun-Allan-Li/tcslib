<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.exercise7_31a_repeatedScope_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated-Variable Cloning Counterexample

**Claim.** The repeated-not-equal experiment has optimum $0$, while its two-clone version has optimum at least $1/2$.

**Proof.** The optimum of the original repeated-not-equal experiment is $0$ (`repeatedNotEqualExperiment_optimum`). In the two-clone experiment, the specified assignment has value $1/2$ (`repeatedNotEqual_clone_value`). Every assignment’s value is at most the optimum (`value_le_optimum`), so this particular assignment certifies that the cloned experiment’s optimum is at least $1/2$.

**Key facts.** `FABL.WeightedConstraintExperiment.repeatedNotEqualExperiment_optimum`, `FABL.WeightedConstraintExperiment.repeatedNotEqual_clone_value`, `FABL.WeightedConstraintExperiment.value_le_optimum`.

**Caveat.** The supplied formal theorem proves this counterexample only; it does not establish the broader reduction and deletion claims in the informal description.
