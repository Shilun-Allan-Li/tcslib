<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.step_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance halts the machine

**Claim.** If the instruction at the program counter of $c$, with rejection used as the default out-of-range instruction, is accept, then one step of $P$ from $c$ returns the acceptance result.

**Proof.** The step function examines the instruction at the current program counter. Under the hypothesis that this instruction is accept, its defining accept case returns the right-hand outcome with Boolean value true. Thus the step is the acceptance result.
