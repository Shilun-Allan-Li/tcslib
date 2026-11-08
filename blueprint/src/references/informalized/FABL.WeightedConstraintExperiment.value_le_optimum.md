<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.value_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Bounded by the Optimum

**Claim.** For a weighted constraint experiment with finite variable set and finite nonempty domain, every assignment has value at most the experiment’s optimum.

**Proof.** Finiteness ensures that the value function on assignments attains a maximum. The chosen optimal assignment is a maximizer, so the value at any assignment is at most the value at that maximizer. By definition, that maximum value is the optimum.
