<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.detM_step_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting Step for Memory Operations

**Claim.** Whenever the compiled machine is in a state where the memory-instruction map is defined, its next step halts and appends the prescribed Boolean value to the output.

**Proof.** A defined memory instruction at a compiled state can occur only at a program-running state $(l,\mathrm{start})$, where the underlying memory-augmented program has a memory instruction at $l$. By the specification of the deterministic part of that program, this instruction is replaced by the return instruction outputting $\beta$ (`MARM.detPart_mem`). The return instruction has no call specification, and its transition emits $\beta$ and has no successor state. Consequently the compiled transition takes its ordinary-program branch, applies exactly that return action, and halts while appending $\beta$ to the existing output.

**Key facts.** `Complexity.LogProg.mop_spec`, `Complexity.LogProg.MARM.detPart_mem`.
