<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_compileStmt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled Statement Length

**Claim.** For every code layout $G$, statement $s$, and starting position $p$, the compiled code for $s$ has length equal to the size of $s$ for frame width $G.F$.

**Proof.** Proceed by structural induction on the statement, allowing the starting position to vary. The position affects branch destinations but not the number of instructions. The empty statement compiles to the empty list, so both lengths are zero. For an assignment, the compiled expression contributes its size, and the address calculation and store contribute two more instructions, giving the stated size. For a store, the two compiled expressions contribute their respective sizes and the final store contributes one instruction. For a sequence, the two compiled statement lists concatenate; applying the induction hypotheses to each gives the sum of their sizes. For a conditional, the condition contributes its size, the first branch contributes its size, the unconditional jump contributes one instruction, and the second branch contributes its size. The condition-length theorem and the induction hypotheses therefore give the conditional's defining size. For a loop, the condition and body contribute their sizes, and the final jump contributes one instruction, again matching the definition. Finally, a call compiles to its call code followed by the two instructions that store the returned value. The call-code length theorem gives the call size, so the total is the statement size for a call.

**Key facts.** `Light.Compiler.length_compileExpr`, `Light.Compiler.length_compileCond`, `Light.Compiler.length_callCode`.
