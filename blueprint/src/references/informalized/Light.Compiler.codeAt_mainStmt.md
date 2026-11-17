<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_mainStmt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Location of the main statement

**Claim.** For every light program $P$, natural number $p_0$, and Boolean flag $dec$, the compiled main statement is a prefix of the compiled program beginning at position $4$.

**Proof.** The main code is the concatenation of the compiled main statement and the remaining tail code. Since the main code is a prefix of the compiled program beginning at position $4$ (\texttt{codeAt\_mainCode}), its initial block—the compiled main statement—is also a prefix there.

**Key facts.** `Light.Compiler.codeAt_mainCode`, `WordRAM.CodeAt.left`.
