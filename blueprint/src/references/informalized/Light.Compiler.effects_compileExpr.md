<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.effects_compileExpr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effects of Compiled Expressions

**Claim.** For a framed memory, a safe expression whose variables fit within the frame and whose temporary index satisfies the height bound is evaluated into temporary cell $k$, with changes confined to the address scratch cell and temporary cells from $k$ through $2F$.

**Proof.** Proceed by structural induction on the expression, generalizing the temporary index and initial memory. In every case, the height bound ensures that $cT(k)$ lies in the permitted temporary set (`Light.Compiler.cT_mem_temps_of_height`).

For a constant, the digit-code theorem shows that its compiled binary digits leave the represented number in cell $cT(k)$ and change no other cell except that one (`Light.Compiler.effects_digitsCode`). The binary digits are all less than $2$, and the constant-one cell supplies the increment used by the code. The resulting single-cell modification is within the temporary region.

For a variable, the first instruction computes its stack address by subtracting the pool-stored offset from the frame pointer. The frame relation and the stack-address identity (`Light.Compiler.cStack_sub`) identify this address with the cell for that local variable. The following load therefore puts the variable’s value in $cT(k)$ (`WordRAM.effect_sub`, `WordRAM.effect_load`). The bounds ensure the variable index and stack address are valid; the two writes affect only the address scratch cell and $cT(k)$.

For an operation, apply the induction hypothesis to the left operand at $k$. Its changes are within the scratch region, so the frame relation transfers to the resulting memory (`Light.Compiler.temps_subset_scratch`, `Light.Compiler.Framed.same`). Apply the induction hypothesis to the right operand at $k+1$. The left result remains available there because the right computation preserves cells outside its own temporary region. The compiled operation then writes the evaluation of the two operand values into $cT(k)$ (`Light.Compiler.effect_instr`). The operand bounds follow from the variable and height bounds for the compound expression. Combining the two preservation statements and the final write confines all changes to the permitted set (`WordRAM.AgreeOutside.trans`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.update`).

For a load, the induction hypothesis first computes the address expression in $cT(k)$. Safety makes this address nonnegative and within the valid memory range, so the loaded word is the state’s value at that address (`Light.Compiler.Sizes.inRange_addr`, `Light.Compiler.Rel.read`, `WordRAM.effect_load`). The address is outside the temporary and scratch set, hence the preceding computation has not changed its contents (`WordRAM.AgreeOutside.cell`). The final load writes that value into $cT(k)$, preserving the claimed support bound.

**Key facts.** `Light.Compiler.cT_mem_temps_of_height`, `Light.Compiler.effects_digitsCode`, `Light.Compiler.cStack_sub`, `WordRAM.effect_sub`, `WordRAM.effect_load`, `Light.Compiler.temps_subset_scratch`, `Light.Compiler.Framed.same`, `Light.Compiler.effect_instr`, `WordRAM.AgreeOutside.trans`, `WordRAM.AgreeOutside.mono`, `WordRAM.AgreeOutside.update`, `Light.Compiler.Sizes.inRange_addr`, `Light.Compiler.Rel.read`, `WordRAM.AgreeOutside.cell`.
