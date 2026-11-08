<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.steps_callLeave -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning From a Procedure Call

**Claim.** Under the stated hypotheses, the machine reaches program counter $\mathrm{ret}$ after $5+2(\mathrm{ret}+1)$ steps, with the frame pointer encoding stack position $q$, the return register encoding $\sigma.loc(0)$, and memory unchanged outside the frame-pointer address and scratch addresses.

**Proof.** The epilogue first loads the saved caller value from the callee frame's local cell $0$ into the return register. The relation identifies that cell's value with $\sigma.loc(0)$ (`Rel.loc_zero`). It next forms the address of the saved return-address cell, then loads the encoded return position into the return register; the stack-position arithmetic follows from `cStack_succ_add`. The next addition restores the frame pointer to the caller's stack position, using the stored pool offset and `cStack_add`. The epilogue then jumps to the dispatcher, with the negative branch representable (`Sizes.inRange_neg_one`). The dispatcher, started with return-register value $\mathrm{ret}$, takes $2(\mathrm{ret}+1)$ steps to reach program counter $\mathrm{ret}$ and leaves $-1$ in that register (`steps_dispatcher`); combining these with the five epilogue instructions gives the claimed count. For memory agreement, each instruction's writes are tracked as updates in scratch locations, while the final frame-pointer update is allowed explicitly. Agreement outside scratch is preserved by the update and monotonicity properties (`AgreeOutside.refl`, `AgreeOutside.update`, `AgreeOutside.mono`), and reads from locations outside the changed set retain their values (`AgreeOutside.read`).

**Key facts.** `Light.Compiler.Rel.loc_zero`, `Light.Compiler.cStack_succ_add`, `Light.Compiler.cStack_add`, `Light.Compiler.Sizes.inRange_neg_one`, `Light.Compiler.steps_dispatcher`, `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.read`.
