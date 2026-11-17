<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One subtraction step

**Claim.** When the instruction at position $pos$ subtracts the contents of registers $k$ and $j$ into register $i$, and those contents encode $a$ and $b$, one step advances to $pos+1$ and leaves register $i$ holding the encoding of $a-b$.

**Proof.** The code prefix identifies the current instruction as subtraction. By the subtraction-effect identity (`WordRAM.effect_sub`), the effect of that instruction on $m$ is the memory obtained by updating register $i$ with the encoding of $a-b$, using the hypotheses that $m(j)$ and $m(k)$ encode $a$ and $b$. Subtraction is a straight instruction, so the one-step execution rule `WordRAM.steps_instr` takes the program counter to $pos+1$ with precisely this effect. Replacing the effect in that execution statement by the equal updated memory proves the claim.

**Key facts.** `WordRAM.effect_sub`, `WordRAM.steps_instr`.
