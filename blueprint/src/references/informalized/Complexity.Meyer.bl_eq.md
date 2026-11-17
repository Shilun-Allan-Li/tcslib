<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.bl_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Blank Tapes

**Claim.** The tape that is blank at every integer cell equals the tape obtained by storing the empty word starting at cell zero.

**Proof.** At a negative cell, both tapes return no symbol. At a nonnegative cell, the tape represented by the empty word also returns no symbol, since there is no entry of that word at any index. Thus the two functions agree at every integer cell and are equal.
