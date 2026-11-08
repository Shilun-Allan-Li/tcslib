<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_pair_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair selection inverts the slot map

**Claim.** Selecting a role at its physical call-layout index returns that same role, for either the argument or capture role.

**Proof.** There are two roles to check. For the argument role, its index is $0$, and the selector returns the argument role at index $0$. For the capture role, its index is the final slot, whose value is the designated capture index; the selector returns the capture role there. Hence selection after indexing returns the original role in both cases.
