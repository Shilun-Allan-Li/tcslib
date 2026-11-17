<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.steps_jump -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative branch jump

**Claim.** If the instruction at position $\mathrm{pos}$ branches on whether register $cNEG$ is negative, and that register contains the word encoding $-1$ within the signed range, then one step sends the program counter to $l$ and leaves memory unchanged.

**Proof.** Apply the one-step branch rule (`WordRAM.steps_bltz`) with tested value $v=-1$. The hypotheses identify the register contents with the word encoding this value and provide the required signed-range condition. Since $-1<0$, the branch target in the rule is $l$; a branch instruction does not modify memory. This is exactly the claimed one-step execution.

**Key facts.** `WordRAM.steps_bltz`.
