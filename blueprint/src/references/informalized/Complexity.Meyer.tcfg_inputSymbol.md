<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachine.lean :: Complexity.Meyer.tcfg_inputSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol Independent of Work Tapes

**Claim.** The associated configuration reads the same input symbol when its work tapes and output are replaced by blank tapes and an empty output, provided its state and input-head position are kept fixed.

**Proof.** The input symbol read from a configuration depends only on its input word and input-head position. The two configurations have the same input word and the same position, so their input symbols agree; their work-tape contents, work-head positions, and output words do not enter this computation. The equality is definitional.
