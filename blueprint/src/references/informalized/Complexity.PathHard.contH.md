<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.contH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Under Equal Registers

**Claim.** If two register records are equal, any guarded halting run starting from the second record also gives the same halting run starting from the first record, with the same label and answer.

**Proof.** Equal register records have equal register vectors under the register-to-vector map. Transport the given halting statement along this equality. The run length, terminal answer, and guard condition are preserved.
