<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_mainCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Location of the main code

**Claim.** For every light program $P$, natural number $p_0$, and Boolean flag $dec$, the compiled main code is a prefix of the compiled program beginning at position $4$.

**Proof.** The compiled program is a concatenation beginning with the header and followed by the main code. The whole program is a prefix of itself at position $0$ (\texttt{WordRAM.codeAt\_self}). Taking the first block successively extracts the header, and taking the following block extracts the main code at the position immediately after it. The header occupies four instructions, so this position is $4$.

**Key facts.** `WordRAM.codeAt_self`, `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`.
