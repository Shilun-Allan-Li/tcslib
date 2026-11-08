<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NDCodes.lean :: Turing.NDMachineCode.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Encoded Machine

**Claim.** If the decoding scheme returns a machine when given its encoding followed by any number of padding bits equal to $1$, then decoding the encoding of any machine returns that machine.

**Proof.** Apply the assumed decoding property with zero padding bits. Appending zero copies of the padding bit leaves the encoding unchanged, so the stated property gives that decoding the encoding of $M$ is $M$.
