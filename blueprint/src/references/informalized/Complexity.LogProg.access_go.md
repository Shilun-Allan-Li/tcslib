<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_go -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stationary State Change

**Claim.** The action that leaves the input head, work tapes, and work-tape heads fixed while changing the state to $s'$ sends the specified initial configuration exactly to the corresponding configuration in state $s'$.

**Proof.** By definition, the action sets the new state to $s'$, writes nothing, makes no work-tape head movements, emits no output, and makes no input-head movement. The zero-movement identity for the input head (`Turing.moveInputPos_zero`) therefore preserves its position. The tape contents and all work-tape heads remain as prescribed, so every component agrees with the target configuration.

**Key facts.** `Turing.moveInputPos_zero`.
