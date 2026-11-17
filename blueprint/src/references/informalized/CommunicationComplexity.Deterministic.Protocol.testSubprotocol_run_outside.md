<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.testSubprotocol_run_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Test protocol on non-reaching inputs

**Claim.** If an input pair does not reach the chosen subprotocol, running the test subprotocol gives the same output as running $q_{\mathrm{out}}$.

**Proof.** First suppose Alice's input is outside her reach set. Her test returns false, so the conjunction of the two test bits is false regardless of Bob's bit, and the protocol selects $q_{\mathrm{out}}$. Otherwise Alice's input is in her reach set. Since the pair does not reach the subprotocol, Bob's input must then be outside his reach set; his test returns false, again making the conjunction false and selecting $q_{\mathrm{out}}$. In either case the resulting output agrees with running $q_{\mathrm{out}}$.
