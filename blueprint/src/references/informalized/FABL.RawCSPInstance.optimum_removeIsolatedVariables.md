<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RawCSPInstance.optimum_removeIsolatedVariables -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum After Removing Isolated Variables

**Claim.** For a raw constraint satisfaction instance with finite variable set and finite nonempty domain, removing isolated variables leaves the optimum value unchanged.

**Proof.** Unfold the two optima and prove both inequalities. First, take an optimal assignment on the participating variables. The extension result (`exists_raw_assignment_same_value`) gives an assignment on all variables with the same value. That value is at most the original optimum, since every assignment is bounded by the optimum (`RawCSPInstance.value_le_optimum`). Thus the reduced instance’s optimum is at most the original one. Conversely, restrict an optimal assignment of the original instance to the participating variables. Restriction preserves value (`value_restrictAssignment`), and that restricted assignment’s value is at most the reduced instance’s optimum (`CSPInstance.value_le_optimum`). This proves the reverse inequality and hence equality.

**Key facts.** `FABL.RawCSPInstance.exists_raw_assignment_same_value`, `FABL.RawCSPInstance.value_le_optimum`, `FABL.RawCSPInstance.value_restrictAssignment`, `FABL.CSPInstance.value_le_optimum`.
