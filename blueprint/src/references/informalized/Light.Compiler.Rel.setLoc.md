<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.setLoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a local variable

**Claim.** Updating one local variable and the corresponding stack cell preserves the storage relation, provided the frame pointer is positive.

**Proof.** Let the modified memory be obtained by replacing the value at the stack address for local $x$ with the encoding of $v$. It agrees with the original memory outside that single address: agreement is reflexive, and updating a memory at an address preserves agreement away from that address (`WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`). The updated address is not a constant or pool address, so the relation-construction result applies (`Light.Compiler.Rel.of_agreeOutside`). The frame-pointer and ordinary-memory clauses remain unchanged because their addresses are outside the updated cell. For a local index $y$, split into $y=x$ and $y\ne x$. In the first case, both the updated local value and updated stack cell encode $v$. In the second, the memory update leaves the stack cell unchanged, while the updated state leaves local $y$ unchanged; the original relation supplies the required equality.

**Key facts.** `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `Light.Compiler.Rel.of_agreeOutside`.
