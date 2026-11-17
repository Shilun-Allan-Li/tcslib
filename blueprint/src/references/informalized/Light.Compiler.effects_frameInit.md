<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.effects_frameInit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effects of Frame Initialization

**Claim.** Under the stated pointer, pool, and stack-bound hypotheses, frame initialization puts the requested temporary value, or zero when the index is beyond the supplied temporaries, into each new stack cell. The resulting memory agrees with its initial value outside the address scratch cell and the stack cells from $q'$ through $Q-1$.

**Proof.** Proceed by induction on the number $F'$ of initialized cells. When $F'=0$, there are no cells to check, and the memory is unchanged, so the agreement claim follows by reflexivity. For the successor step, apply the induction hypothesis to the first $F'$ cells. By the successor decomposition of the code (`frameInit_succ`), the remaining two instructions subtract the pool offset $2F'$ from the new-frame pointer and store either temporary $F'$ or the zero cell. The pointer and pool hypotheses identify the subtraction result with the address of stack cell $q'+F'$, using the stack-offset identity (`cStack_sub`). The store therefore writes the required value there. For earlier cells, the two updates do not change their addresses, so their values remain as supplied by induction. Finally, the induction hypothesis gives agreement away from the address scratch cell and the first $F'$ stack cells; the two new updates preserve agreement outside the enlarged writable set, by `AgreeOutside.update`.

**Key facts.** `Light.Compiler.frameInit_succ`, `WordRAM.effects_append`, `WordRAM.effect_sub`, `Light.Compiler.cStack_sub`, `WordRAM.effect_store`, `WordRAM.AgreeOutside.update`, `WordRAM.AgreeOutside.refl`.
