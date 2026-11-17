<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RawCSPInstance.participatingConstraint_satisfiedIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction Under Restriction

**Claim.** For any constraint of a raw instance and any assignment to all variables, its satisfaction indicator agrees with the indicator of the corresponding constraint on participating variables under the restricted assignment.

**Proof.** The corresponding constraint on participating variables has the same predicate, and its scope sends each input position to the original variable together with evidence that the variable participates. Restricting the assignment reads the value at the underlying original variable. Consequently, at every input position the predicate receives exactly the same value in both evaluations. Their Boolean outcomes, and therefore their satisfaction indicators, agree.
