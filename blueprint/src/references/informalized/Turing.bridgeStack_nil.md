<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStack_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation of the Empty Stack

**Claim.** The tape representation of the empty stack is blank at every integer cell.

**Proof.** Fix an integer cell. For the empty stack, the condition determining whether that cell represents a stack entry fails: adding the stack length, which is zero, does not give a nonnegative index for a negative cell. For a nonnegative cell, the resulting list lookup in the empty list is absent. In either case the represented tape value is blank, so the representation agrees everywhere with the function constantly equal to blank.
