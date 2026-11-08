<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_store -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step store

**Claim.** Under the stated code, memory, and range hypotheses, one step from $(pos,m)$ reaches program counter $pos+1$ and updates address $a$ with the word $m(j)$.

**Proof.** The code prefix identifies the instruction at position $pos$ as the store instruction. Its effect writes $m(j)$ at address $(m(i)).toInt$. Since $m(i)$ is the encoding of $a$ and $a$ is in the signed range, the signed interpretation of that encoding is $a$. Thus the store effect is exactly the memory update at address $a$ with value $m(j)$ (the store-effect identity, `WordRAM.effect_store`). A straight instruction takes one step to the next program position with its prescribed effect (`WordRAM.steps_instr`), giving the stated one-step execution.

**Key facts.** `WordRAM.effect_store`, `WordRAM.steps_instr`.
