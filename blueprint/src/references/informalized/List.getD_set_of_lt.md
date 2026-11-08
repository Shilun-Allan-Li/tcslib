<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_set_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup after replacing an entry

**Claim.** If position $q$ is in range, then lookup after replacing that entry by $a$ gives $a$ at $q$ and agrees with the original defaulted lookup at every other index.

**Proof.** Express defaulted lookup through optional indexed access, with the default used when the index is out of range. The rule for optional lookup after setting a list entry shows that the result is the replacement exactly when the queried index equals $q$; otherwise it is the original optional entry. Since $q$ is in range, converting these cases back to defaulted lookup gives the stated formula, including the out-of-range case.
