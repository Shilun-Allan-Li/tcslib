<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.clonedLongCodeWeightedExperiment_value_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Preserved by Cloning

**Claim.** For every positive integer $M$, assigning each clone the sign assigned to its original variable preserves the value of the cloned long-code constraint experiment: it equals the original long-code experiment’s acceptance value for the table.

**Proof.** The value of a cloned weighted constraint experiment under the constant clone assignment equals the value of the original experiment under the corresponding assignment (`clone_value_constantCloneAssignment`). Apply this to the long-code weighted experiment and its long-code assignment. The original weighted experiment’s value under that assignment is the long-code experiment value (`longCodeWeightedExperiment_value`), so the claimed equality follows.

**Key facts.** `FABL.WeightedConstraintExperiment.clone_value_constantCloneAssignment`, `FABL.RegularUniqueGame.longCodeWeightedExperiment_value`.
