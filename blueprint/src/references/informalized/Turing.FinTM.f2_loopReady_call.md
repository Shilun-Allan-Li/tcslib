<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopReady_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ready Configuration as Startup Call

**Claim.** For every fuel configuration, the ready configuration equals the startup call on the body’s initial configuration, with release disabled, no flag, and the fuel word and configuration inherited from the fuel configuration.

**Proof.** Compare the two configurations field by field. Their states, input-head positions, and outputs agree by their definitions. On the body tapes, the startup call contains the body’s initial configuration: the initial state, blank tapes, and zero head positions. The dedicated flag tape is blank in both descriptions. The fuel tapes and their head positions are the same as in the given fuel configuration, and the payload tape contains that configuration’s output as the fuel word. Thus every tape, head, and remaining configuration field agrees, proving equality.
