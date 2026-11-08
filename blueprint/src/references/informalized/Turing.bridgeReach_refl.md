<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeReach_refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of Machine Reachability

**Claim.** For any multi-tape Turing machine on a fixed input and any configuration, that configuration is reachable from itself.

**Proof.** Reachability means that some finite number of machine steps takes the first configuration to the second. Choose zero steps. Iterating the machine’s step function zero times leaves every configuration unchanged, so the configuration is reachable from itself.
