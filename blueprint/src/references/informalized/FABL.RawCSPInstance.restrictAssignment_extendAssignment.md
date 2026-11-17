<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RawCSPInstance.restrictAssignment_extendAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Recovers an Extended Assignment

**Claim.** For a nonempty domain, extending an assignment on participating variables to all variables and then restricting it back recovers the original assignment.

**Proof.** Compare the two assignments at an arbitrary participating variable. That variable satisfies the participation condition by its definition, so the extension uses the given assignment at that variable rather than the chosen default domain element. The resulting value is exactly the original assignment’s value there. Since this holds at every participating variable, the assignments are equal.
