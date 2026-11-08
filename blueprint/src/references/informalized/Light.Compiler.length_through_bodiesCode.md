<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.length_through_bodiesCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Through Procedure Bodies

**Claim.** For every program $P$, main procedure index $p_0$, and Boolean flag $d$, the concatenation of the head code, main code, and all procedure body code has length equal to the dispatcher position determined by $P$ and $d$.

**Proof.** First, the head code followed by the main code has length equal to the first procedure-body position, by the main-code length calculation (`length_through_mainCode`). The body-code length calculation (`length_bodiesCode`) says that, starting at any position, the position plus the length of the code for a list of bodies equals the corresponding end position. Apply it to the program bodies starting at the first-body position. By definition, that end position is the dispatcher position. Combining these equalities gives the asserted total length.

**Key facts.** `Light.Compiler.length_through_mainCode`, `Light.Compiler.length_bodiesCode`.
