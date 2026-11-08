<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Borrow_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single Borrow Transition

**Claim.** In the borrow state, with head at the prefix boundary and tape containing $\mathrm{pre}\,\mathrm{bs}$, one step has the stated outcomes in the empty, leading-$1$, and leading-$0$ cases, preserving input position and output.

**Proof.** The machine reads the work-tape cell at the prefix boundary. The buffer-read fact (`Complexity.a2Buffer_read`) identifies that symbol as the first bit of $\mathrm{bs}$, or blank when $\mathrm{bs}$ is empty. If the suffix is empty, the blank-cell transition enters the result state with failure and moves left. If its first bit is $1$, the machine writes $0$, enters the result state with success, and moves left. If its first bit is $0$, it writes $1$, stays in the borrow state, and moves right. The buffer-write fact (`Complexity.a2Buffer_write`) identifies the updated tape with the corresponding concatenated word. In all cases the transition makes no input-head movement and emits no output, so those parts of the configuration remain unchanged.

**Key facts.** `Complexity.a2Buffer_read`, `Complexity.a2Buffer_write`, `Turing.moveInputPos_zero`.
