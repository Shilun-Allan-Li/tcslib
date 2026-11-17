<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.steps_setVar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled assignment to a variable

**Claim.** Under the stated frame and code hypotheses, with $x<F$, source address $c$ holding the word for $v$, and $c\ne cADDR$, two steps store $v$ in local variable $x$. The resulting memory represents the updated state at depth $q$ and agrees with the original memory outside the writable-address set.

**Proof.** The first instruction computes the destination address. The frame pointer contains the encoding of $cStack(q)$, and the pool contains the encoding of offset $2x$. The subtraction-step rule (`WordRAM.steps_sub`) therefore writes their difference into $cADDR$; the address identity `Light.Compiler.cStack_sub` identifies this difference as $cStack(q+x)$. This update is confined to the scratch set, so the original relation to the state is preserved by `Light.Compiler.Rel.same`.

The second instruction stores the contents of register $c$ at the address in $cADDR$. The stack-range fact `Light.Compiler.Sizes.inRange_stack`, together with the frame bounds, makes this a valid represented stack address. The store-step rule (`WordRAM.steps_store`) performs exactly that update. Since $c\ne cADDR$, the first instruction's update to the address register has not changed the source value. The resulting memory is therefore the original memory updated at $cStack(q+x)$ with the word for $v$. The representation update lemma (`Light.Compiler.Rel.setLoc`) gives the relation to the state whose local variable $x$ is set to $v$. For the agreement claim, the address-register update is in the scratch set and hence in the writable set (`Light.Compiler.scratch_subset_writable`); the subsequent update is also writable. The update and monotonicity properties of agreement (`WordRAM.AgreeOutside.update`, `WordRAM.AgreeOutside.mono`) give the required agreement outside the writable set. Combining the two one-step runs uses `WordRAM.Steps.trans`.

**Key facts.** `WordRAM.steps_sub`, `Light.Compiler.cStack_sub`, `Light.Compiler.Rel.same`, `Light.Compiler.Sizes.inRange_stack`, `WordRAM.steps_store`, `Light.Compiler.Rel.setLoc`, `WordRAM.AgreeOutside.update`, `Light.Compiler.scratch_subset_writable`, `WordRAM.AgreeOutside.mono`, `WordRAM.Steps.trans`.
