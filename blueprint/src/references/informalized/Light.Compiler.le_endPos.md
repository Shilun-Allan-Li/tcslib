<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.le_endPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End Position Is Nondecreasing

**Claim.** Advancing through any finite list of statements, adding each statement's size and an epilogue of size five, never decreases the starting position.

**Proof.** Proceed by induction on the list. For the empty list, the end position is the starting position. For a nonempty list with first statement $b$, its size and the epilogue size are natural numbers, so the updated position $pos+\mathrm{size}(b)+5$ is at least $pos$. By induction, processing the remaining list from that updated position ends at a position at least as large as the updated position. Transitivity gives the result.
