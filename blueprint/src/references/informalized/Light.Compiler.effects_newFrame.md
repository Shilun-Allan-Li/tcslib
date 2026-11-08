<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/CallFrames.lean :: Light.Compiler.effects_newFrame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effects of New-Frame Code

**Claim.** Given the framed-state assumptions, sufficient stack capacity, initialized argument temporaries, and a return position within the dispatcher bound, executing new-frame code establishes the relation for the new frame at position $q+F+1$. Its return-address stack cell contains $r$, and the memory agrees with its initial value outside the writable locations for that frame.

**Proof.** Let $R$ be the relation on the original frame, and first execute the instruction that computes the new-frame pointer by subtracting the pool offset $2(F+1)$ from the frame pointer. The pool and frame-pointer conditions, together with `cStack_sub`, identify the result as stack position $q+F+1$. The original relation remains valid after this scratch-register change: `Rel.beyond` says the represented state is preserved when memory agrees outside scratch cells and the stack beyond the current frame.

Next execute frame initialization for the $F$ local cells, using `effects_frameInit`. Each new local receives its corresponding temporary when an argument is present and otherwise receives zero. Its agreement guarantee, combined with the first update, lets `Rel.beyond` preserve the original frame relation through these writes. The following addition computes the address of stack cell $q+F$ from the new-frame pointer, by `cStack_succ_add`; storing the return position there is justified by the pool value for $r$ and the in-range stack property (`Sizes.inRange_stack`). The updates so far affect only scratch locations and the stack region beyond the old frame, and `AgreeOutside.update` and `AgreeOutside.trans` track their combined effect.

The final addition sets the frame pointer to the new-frame pointer, since the zero cell contains zero. The preserved relation and the established local values then give the new `Rel` via `Rel.of_agreeOutside`: the frame pointer is at $q+F+1$, each local has its argument value or zero, and ordinary memory still represents the original state. The return-cell calculation gives the second conclusion. Finally, the agreement accumulated for scratch cells and the stack region, together with the inclusions of those sets in `Writable` (`scratch_subset_writable`, `stack_subset_writable`), yields agreement outside the claimed writable set.

**Key facts.** `WordRAM.effects_append`, `WordRAM.effect_sub`, `Light.Compiler.cStack_sub`, `Light.Compiler.Rel.beyond`, `Light.Compiler.effects_frameInit`, `WordRAM.AgreeOutside.trans`, `Light.Compiler.cStack_succ_add`, `WordRAM.effect_add`, `WordRAM.effect_store`, `Light.Compiler.Sizes.inRange_stack`, `WordRAM.AgreeOutside.update`, `Light.Compiler.Rel.of_agreeOutside`, `Light.Compiler.scratch_subset_writable`, `Light.Compiler.stack_subset_writable`, `WordRAM.AgreeOutside.mono`.
