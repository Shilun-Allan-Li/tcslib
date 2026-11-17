<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RawCSPInstance.exists_raw_assignment_same_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending an Assignment Without Changing Value

**Claim.** An assignment to the variables participating in constraints can be extended to all variables so that its value in the instance with isolated variables removed equals the extended assignment’s value in the original instance.

**Proof.** Extend the given assignment to all variables using the nonemptiness of the domain, and call the extension $a$. Restricting $a$ back to the participating variables recovers the original assignment (`restrictAssignment_extendAssignment`). The value preservation identity for restriction says that the value of $a$ in the original instance equals the value of its restriction in the instance with isolated variables removed (`value_restrictAssignment`). Combining these equalities gives the required value identity.

**Key facts.** `FABL.RawCSPInstance.value_restrictAssignment`, `FABL.RawCSPInstance.restrictAssignment_extendAssignment`.
