<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopControl_payload -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload-Only Controller Actions

**Claim.** With no flag or counter operation and with only a payload-head movement, the controller action equals the right-block extension of the corresponding one-tape action.

**Proof.** The right-block extension leaves all newly added tapes unchanged and applies the one-tape action on the final block. On every index in the added block except its sole tape, the controller supplies no write and zero movement. On that sole tape—the payload tape—it supplies no write and the chosen movement. The input direction is zero in both actions, and their emitted bit and successor state agree. Hence their action components coincide.
