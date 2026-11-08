<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/WholeProgram.lean :: Light.Compiler.start_mainStmt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Simulation Setup

**Claim.** Under the stated fit and boundedness hypotheses, and given memory related to the state at the main-frame stack position, the main statement satisfies the starting conditions at depth $0$, main code position, and main-frame stack position.

**Proof.** Use the assumed memory relation directly for the relational part of the starting conditions. The main frame begins at a positive stack position, and the stack capacity bound follows from the fact that the stack allocation includes at least the main frame and one additional frame-size block (`frame_le_stackCells`). The compiled main statement is located at `mainPos` (`codeAt_mainStmt`). Its size is $2F+11$ (`size_mainStmt`), so the bound $2F+17\leq\mathrm{dispPos}$ ensures it ends before the dispatcher. Its width is $3$ (`width_mainStmt`), which is at most $F$ because every frame size is at least $3$ (`three_le_frameSize`). The state boundedness condition is the given hypothesis. Finally, at depth zero the required room is bounded by the allocated stack capacity, using the definition of `stackCells`; the remaining arithmetic follows from these definitions.

**Key facts.** `Light.Compiler.frame_le_stackCells`, `Light.Compiler.codeAt_mainStmt`, `Light.Compiler.size_mainStmt`, `Light.Compiler.two_mul_frameSize_add_le_dispPos`, `Light.Compiler.width_mainStmt`, `Light.Compiler.three_le_frameSize`.
