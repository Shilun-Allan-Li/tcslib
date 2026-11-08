<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStore_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Storage of the empty word

**Claim.** The assignment that places the empty word on the main stack and leaves every other stack empty assigns the empty word to every stack.

**Proof.** Evaluate the assignment at an arbitrary stack. Each of the four possible stack names selects one of the four entries in the assignment, and all four entries are empty. Hence the resulting function is constantly the empty word.
