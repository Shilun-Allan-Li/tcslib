<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.uHead_true_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary-head output after true

**Claim.** For every finite bit string $w$, the unary-head transducer outputs a true bit followed by its output on $w$ when the input begins with true.

**Proof.** The initial true bit, read in the true state, emits a true bit. The transition then leaves the state true, so the remaining input $w$ is processed exactly as it would be when given on its own. Concatenating these outputs gives the stated result.
