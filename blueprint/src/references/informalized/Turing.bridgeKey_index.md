<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeKey_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round Trip on Stack Names

**Claim.** For every compiled-machine stack name, mapping it to its work-tape index and then back to a stack name returns the original name.

**Proof.** There are four stack names: main, reverse, auxiliary, and stack. In each case, the index assignment selects its corresponding one of the four work tapes, and the reverse assignment sends that index back to the same stack name. Hence the composite is the identity on every stack name.
