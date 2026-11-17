<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.two_mul_frameSize_add_le_dispPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound on dispatcher position

**Claim.** For every program $P$ and every Boolean choice of whether to use the decrementing tail code, the dispatcher position is at least $2$ times the frame size of $P$ plus $17$.

**Proof.** The dispatcher position is obtained by starting at the first body position and then advancing through the program statements, adding nonnegative statement sizes and epilogue lengths. Thus the first body position is no larger than the dispatcher position (`le_endPos`). By definition, the first body position is the tail position plus the length of the tail code. The main-statement size formula gives the tail position as $2F+15$, where $F=\mathrm{frameSize}(P)$, and the tail code has length $5$ when the decrementing code is used and $2$ otherwise (`length_tailCode`). In either case its length is at least $2$. Therefore the dispatcher position is at least $(2F+15)+2=2F+17$, as required (`size_mainStmt`).

**Key facts.** `Light.Compiler.le_endPos`, `Light.Compiler.size_mainStmt`, `Light.Compiler.length_tailCode`.
