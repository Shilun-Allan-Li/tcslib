<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.codeAt_dispatcher_dispPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatcher location in the compiled program

**Claim.** For every finite statement list $P$, natural number $p_0$, and Boolean flag $dec$, the dispatcher for $|P|$ procedures is a prefix of the compiled program beginning at the dispatcher position determined by $P$ and $dec$.

**Proof.** The compiled program is a concatenation whose fourth block is the dispatcher, after the header, main code, and compiled procedure bodies. The whole program is a prefix of itself beginning at position $0$ (\texttt{WordRAM.codeAt\_self}). Extracting the dispatcher block from this concatenation gives it as a prefix at the position equal to the length of the preceding blocks. By the length calculation for the header, main code, and procedure bodies (\texttt{length\_through\_bodiesCode}), that position is precisely $\mathrm{dispPos}(P,dec)$.

**Key facts.** `WordRAM.codeAt_self`, `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`, `Light.Compiler.length_through_bodiesCode`, `WordRAM.CodeAt.cast_pos`.
