<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStore_push -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending to the main stack

**Claim.** Updating the assignment with $xs$ on the main stack and all other stacks empty, so that its main stack contains $b$ followed by its previous contents, gives the assignment with $b::xs$ on the main stack and all other stacks empty.

**Proof.** Compare the two assignments at an arbitrary stack. At the main stack, the update replaces the old value $xs$ by $b::xs$, exactly its value in the new assignment. At each of the other three stacks, the update leaves the old empty value unchanged, again matching the new assignment. The functions therefore agree everywhere.
