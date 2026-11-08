<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_bltz -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step conditional branch

**Claim.** If the program at $pos$ begins with a branch to $l$ when the value at address $c$ is negative, the word at $c$ represents $v$, and $v$ is in range, then one step leaves memory unchanged and moves the program counter to $l$ when $v<0$, and to $pos+1$ otherwise.

**Proof.** The code-prefix condition identifies the instruction at $pos$ as the stated branch. The one-step characterization ($\mathrm{Steps.one}$) reduces the claim to computing this step. By the representation hypothesis and the in-range decoding fact ($\mathrm{toInt\_wd}$), the integer decoded from the word at $c$ is exactly $v$. Therefore the branch condition used by the step function is equivalent to $v<0$, so the program counter is $l$ in that case and $pos+1$ otherwise. A branch leaves memory unchanged by its defining step case, proving the result.

**Key facts.** `WordRAM.CodeAt.head`, `WordRAM.Steps.one`, `WordRAM.toInt_wd`.
