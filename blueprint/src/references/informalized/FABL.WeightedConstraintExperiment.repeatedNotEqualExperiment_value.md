<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.repeatedNotEqualExperiment_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Repeated-Not-Equal Experiment

**Claim.** Every assignment of a sign to the single variable gives the repeated-not-equal experiment value $0$.

**Proof.** The experiment has a single outcome, and its predicate tests whether the same variable’s assigned sign is unequal to itself, because that variable occurs in both query positions. A sign is always equal to itself, so the predicate is never satisfied and the payoff is always $0$. Averaging this constant payoff under the experiment’s law leaves the value equal to $0$.
