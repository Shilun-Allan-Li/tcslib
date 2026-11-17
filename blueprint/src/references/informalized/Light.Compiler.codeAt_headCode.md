<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_headCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Header location in the compiled program

**Claim.** For every finite statement list $P$, natural number $p_0$, and Boolean flag $dec$, the header code determined by $P$ and $dec$ is a prefix of the compiled program beginning at position $0$.

**Proof.** The compiled program is defined as a concatenation beginning with the header code. The whole program is a prefix of itself at position $0$ (\texttt{WordRAM.codeAt\_self}); repeatedly taking the first block of this concatenation shows that its initial header block is a prefix at position $0$.

**Key facts.** `WordRAM.codeAt_self`, `WordRAM.CodeAt.left`.
