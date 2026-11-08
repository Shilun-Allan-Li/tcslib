<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPHard.lean :: Turing.PTMCode.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded machine

**Claim.** For a machine code whose decoder returns the encoded machine after any amount of true-bit padding, decoding the encoding itself returns the original machine.

**Proof.** Apply the padding property with zero padding bits. The list of zero true bits is empty, so appending it leaves the encoding unchanged; the property therefore says that decoding the encoding returns the machine.
