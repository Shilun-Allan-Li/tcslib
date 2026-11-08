<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.codeAt_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Instruction segments for a call

**Claim.** If a compiled call is a prefix of the code beginning at $pos$, then its argument-evaluation code followed by new-frame initialisation is a prefix at $pos$, its branch instruction is a prefix at $pos+\mathrm{argsSize}(args)+2F+4$, and the two result-storing instructions are a prefix at $pos+\mathrm{callSize}(F,args)$.

**Proof.** Unfolding the compiled call shows that its code consists of three consecutive blocks: argument evaluation followed by new-frame initialisation, a single branch to the selected procedure entry (defaulting to $0$), and the two instructions that store the call result. Since the whole concatenation is a prefix at $pos$, each block is a prefix at its corresponding offset. The first block has length $\mathrm{argsSize}(args)+2F+4$: argument code has length $\mathrm{argsSize}(args)$ (\texttt{length\_argsCode}) and new-frame initialisation has length $2F+4$ (\texttt{length\_newFrame}). Thus the branch begins at the stated offset. The final two instructions begin after the first block and the one-instruction branch, namely at $pos+\mathrm{argsSize}(args)+2F+5=pos+\mathrm{callSize}(F,args)$.

**Key facts.** `Light.Compiler.length_argsCode`, `Light.Compiler.length_newFrame`, `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`, `WordRAM.CodeAt.cast_pos`.
