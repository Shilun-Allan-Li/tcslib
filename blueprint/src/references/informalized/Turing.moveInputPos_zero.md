<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Configuration.lean :: Turing.moveInputPos_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Move Fixes Position

**Claim.** A move by zero leaves every allowed input-head position unchanged.

**Proof.** Adding zero to the position value leaves it unchanged. Since that value is already in the allowed range, clamping leaves it unchanged as well; hence the resulting position equals the original one.
