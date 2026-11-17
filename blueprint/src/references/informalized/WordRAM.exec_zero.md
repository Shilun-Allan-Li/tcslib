<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.exec_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-step execution

**Claim.** For every word width, program, and configuration, executing for zero steps returns no result.

**Proof.** By the definition of execution, its zero-step case is `none`, regardless of the program counter or memory (`WordRAM.exec`).
