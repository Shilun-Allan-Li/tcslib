<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.repeatedNotEqualExperiment_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Original Experiment Optimum

**Claim.** The optimum of the repeated-not-equal weighted constraint experiment is $0$.

**Proof.** Every assignment of a sign to the single variable has experiment value $0$ (`repeatedNotEqualExperiment_value`). In particular, this holds for the experiment’s chosen optimal assignment. Since the optimum is the value at that assignment, it too is $0$.

**Key facts.** `FABL.WeightedConstraintExperiment.repeatedNotEqualExperiment_value`.
