<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_store -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Store Simulation

**Claim.** If address expression $a$ and value expression $e$ are safe and $a$ evaluates to a permitted address, then storing $e$ at that address is simulated by updating the corresponding memory cell, with cost $\operatorname{cost}(a)+\operatorname{cost}(e)+1$.

**Proof.** Fix a valid starting configuration. Its width bound supplies bounds for both expressions. First evaluate $a$ and $e$ in sequence into temporaries $T_0$ and $T_1$; the paired-expression simulation gives both values and changes only scratch cells. The next machine instruction stores the value in $T_1$ at the address in $T_0$. Safety and the address hypothesis ensure this address is in range, so the machine store updates exactly the cell corresponding to the natural-number address of $a$. The resulting memory satisfies the representation relation for the state with its memory updated, by first transporting the old relation across the scratch-only changes and then applying the relation's memory-update property. Agreement outside writable cells follows because the expression evaluation changes only scratch cells and the final store changes a permitted memory cell. Concatenating the runs and using the expression code lengths gives the claimed endpoint and cost bound.

**Key facts.** `Light.Stmt.width_store_le_iff`, `Light.Compiler.steps_pair`, `Light.Compiler.codeAt_after_pair`, `Light.Compiler.Sizes.inRange_addr`, `WordRAM.Steps.trans`, `WordRAM.steps_store`, `Light.Compiler.Rel.same`, `Light.Compiler.Rel.setMem`, `Light.Compiler.mem_writable_of_addr`, `Light.Compiler.scratch_subset_writable`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.update`, `WordRAM.Steps.cast_pos`, `Light.Compiler.le_stepsPerStep_mul`.
