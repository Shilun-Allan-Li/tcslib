<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeReach_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability After One Step

**Claim.** For any multi-tape Turing machine on a fixed input and any configuration, its one-step successor is reachable from that configuration.

**Proof.** By definition, reachability asks for a number of steps taking the starting configuration to the target. Choose one step: iterating the machine’s step function once sends the configuration exactly to its one-step successor.
