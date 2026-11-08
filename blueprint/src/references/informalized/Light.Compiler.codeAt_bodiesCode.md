<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_bodiesCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compiled bodies occupy their code region

**Claim.** The body code for the statement list, laid out from its first-body position, is a prefix of the compiled program beginning at that position.

**Proof.** The compiled program is a concatenation of its head code, main code, body code, and later sections. The self-prefix property says the entire compiled program is a prefix of itself (`WordRAM.codeAt_self`). Repeatedly taking the suffix after the head and main portions and then the prefix corresponding to the body portion isolates the body code as a prefix beginning just after the head and main code. Their combined length is the first-body position (`Light.Compiler.length_through_mainCode`), so the resulting location is the stated one; `WordRAM.CodeAt.cast_pos` expresses this equality of positions.

**Key facts.** `WordRAM.codeAt_self`, `WordRAM.CodeAt.right`, `WordRAM.CodeAt.left`, `Light.Compiler.length_through_mainCode`, `WordRAM.CodeAt.cast_pos`.
