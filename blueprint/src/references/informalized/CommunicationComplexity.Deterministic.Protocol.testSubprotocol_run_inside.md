<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.testSubprotocol_run_inside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Test protocol on reaching inputs

**Claim.** If an input pair reaches the chosen subprotocol, running the test subprotocol on that pair gives the same output as running $q_{\mathrm{in}}$.

**Proof.** The reach hypothesis says that Alice's input belongs to the reach set and Bob's input belongs to Bob's reach set. The first test therefore returns true, and the second test also returns true. Their conjunction selects the inside branch, so the test protocol continues as $q_{\mathrm{in}}$ and has exactly its output on this input pair.
