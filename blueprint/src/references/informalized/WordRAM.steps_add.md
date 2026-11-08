<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step addition

**Claim.** If the program at position $pos$ begins with an instruction adding the contents of addresses $j$ and $k$ into address $i$, and the words at $j$ and $k$ represent $a$ and $b$, respectively, then one step from $(pos,m)$ reaches program counter $pos+1$ and memory equal to $m$ updated at $i$ with the word representing $a+b$.

**Proof.** The code-prefix condition identifies the instruction at $pos$ as the stated addition instruction. The one-step straight-instruction result then gives a transition to program counter $pos+1$ with memory equal to the effect of that instruction on $m$. By the addition-effect identity ($\mathrm{effect\_add}$), the assumptions about the words at $j$ and $k$ make this effect precisely the update of $m$ at $i$ with $\mathrm{wd}(W,a+b)$. Substituting this memory description gives the claimed one-step relation.

**Key facts.** `WordRAM.effect_add`, `WordRAM.steps_instr`.
