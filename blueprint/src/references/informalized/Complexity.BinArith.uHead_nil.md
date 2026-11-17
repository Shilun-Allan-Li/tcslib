<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uHead_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-head output on empty input

**Claim.** The unary-head transducer outputs the empty string on the empty input.

**Proof.** With no input bits, the transducer has no step at which to emit an output, so its output is empty, directly by the definition of transduction.
