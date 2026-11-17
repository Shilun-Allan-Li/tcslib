<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_startCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Location of the start code

**Claim.** For every light program $P$, procedure index $p_0$, and flag $dec$, the start code is a prefix of the compiled program beginning at position $3\,\mathrm{dispPos}(P,dec)$.

**Proof.** The compiled program is the concatenation of its head code, main code, procedure bodies, dispatcher, and start code. A list is a prefix of itself at position zero; repeatedly taking the suffix after a concatenated prefix therefore shows that the start code is a prefix of the whole program at the position equal to the length of everything before it (`WordRAM.codeAt_self`, `WordRAM.CodeAt.right`). The length theorem for the concatenation through the dispatcher identifies that preceding length as $3\,\mathrm{dispPos}(P,dec)$ (`Light.Compiler.length_through_dispatcher`).

**Key facts.** `WordRAM.codeAt_self`, `WordRAM.CodeAt.right`, `Light.Compiler.length_through_dispatcher`.
