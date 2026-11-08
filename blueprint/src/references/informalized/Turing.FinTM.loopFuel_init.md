<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFuel_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relocated Fuel Initialization

**Claim.** For any Boolean loop body and fuel machine and any Boolean input word, the initial configuration of the relocated fuel source is the relocation of the fuel machine's initial configuration.

**Proof.** The two configurations have the same initial state, input-head position, and empty output. Compare work tapes and head positions by splitting the relocated tape indices into the inserted blank-tape block and the original fuel-machine block. The inserted tapes are blank and have heads at zero, while the original block has exactly the fuel machine's initial blank tapes and zero head positions. Hence all configuration fields agree.
