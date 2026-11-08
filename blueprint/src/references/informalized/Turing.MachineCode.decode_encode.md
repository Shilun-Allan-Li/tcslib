<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.MachineCode.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Unpadded Machine Code

**Claim.** Decoding the unpadded code of every machine returns that machine.

**Proof.** Apply the padding property with zero padding bits. Since appending zero copies of $1$ leaves the encoded word unchanged, the padded-decoding identity is exactly the claimed identity.
