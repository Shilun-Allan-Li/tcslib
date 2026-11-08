<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Codes2Tape.lean :: Turing.MachineCode2.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Unpadded Two-Tape Code

**Claim.** Decoding the unpadded code of each two-tape machine returns that machine.

**Proof.** Apply the padding property with zero padding bits. Appending zero copies of $1$ leaves the encoded word unchanged, so the resulting identity is the desired one.
