<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StatementCode.lean :: Light.Compiler.length_newFrame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# New Frame Length

**Claim.** For all natural numbers $F$, $n$, and $r$, the new frame list with $F$ local slots, $n$ initialized values, and return position $r$ has length $2F+4$.

**Proof.** The new frame consists of one initial instruction, the frame initialization list, and three final instructions. The frame initialization length theorem says that the middle list has length $2F$. Adding the four other instructions gives $2F+4$.

**Key facts.** `Light.Compiler.length_frameInit`.
