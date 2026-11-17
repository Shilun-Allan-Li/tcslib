<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.parallelBit_embed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an Embedded Bit

**Claim.** For an embedding $e$ of the Booleans into a type with decidable equality, decoding $e(b)$ returns $b$.

**Proof.** If $b$ is true, then $e(b)=e(true)$, so the equality test defining the decoder is true. If $b$ is false, injectivity of $e$ implies $e(false)\ne e(true)$, so the test is false. In both cases its Boolean value is $b$.
