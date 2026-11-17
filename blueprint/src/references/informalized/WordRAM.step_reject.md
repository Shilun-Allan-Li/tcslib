<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.step_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection halts the machine

**Claim.** If the instruction at the program counter of $c$, with rejection used as the default out-of-range instruction, is reject, then one step of $P$ from $c$ returns the rejection result.

**Proof.** The step function examines the instruction at the current program counter. Under the hypothesis that this instruction is reject, its defining reject case returns the right-hand outcome with Boolean value false. Thus the step is the rejection result.
