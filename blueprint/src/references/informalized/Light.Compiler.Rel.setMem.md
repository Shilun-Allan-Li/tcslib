<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.setMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a memory cell

**Claim.** Updating a valid light-memory address and the corresponding word-RAM memory cell preserves the storage relation, provided the frame pointer is positive.

**Proof.** Update the word-RAM memory at address $a$, and apply the relation-construction result using agreement outside the singleton containing $a$ (`WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `Light.Compiler.Rel.of_agreeOutside`). Since $a$ is nonnegative, it is not one of the designated negative constant, pool, or stack addresses, so the required disjointness and the unchanged frame-pointer and local clauses hold. For each ordinary memory address $b$ below the space limit, split according to whether $b$ equals the natural-number address corresponding to $a$. At that address, nonnegativity ensures the integer and natural addresses correspond, and both updates assign the encoding of $v$. At every other address the word-RAM update leaves the old value in place, and the light-memory update leaves the corresponding value unchanged; the old relation supplies their equality.

**Key facts.** `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `Light.Compiler.Rel.of_agreeOutside`.
