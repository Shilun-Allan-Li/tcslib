<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.steps_load -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step load

**Claim.** If the program at $pos$ begins with an instruction loading into address $i$ the word at the address stored at $j$, the word at $j$ represents $a$, and $a$ is in range, then one step reaches program counter $pos+1$ with memory obtained by updating $m$ at $i$ with $m(a)$.

**Proof.** The code-prefix condition identifies the first instruction as the stated load. The one-step straight-instruction result gives the next configuration with memory equal to the effect of this load on $m$. By the load-effect identity ($\mathrm{effect\_load}$), the representation of the word at $j$ together with the in-range decoding hypothesis makes that effect exactly the update of $m$ at address $i$ with $m(a)$. Substituting this effect into the one-step result proves the claim.

**Key facts.** `WordRAM.effect_load`, `WordRAM.steps_instr`.
