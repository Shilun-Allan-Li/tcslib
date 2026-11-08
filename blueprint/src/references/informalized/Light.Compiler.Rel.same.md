<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.same -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation outside scratch addresses

**Claim.** If a memory satisfies the storage relation and another memory agrees with it outside the scratch addresses, then the second memory satisfies the same storage relation.

**Proof.** Apply the result on constructing a relation from agreement outside a set (`Light.Compiler.Rel.of_agreeOutside`) with the scratch set. Its disjointness from the constant and pool addresses ensures those stored encodings are preserved. The frame pointer, each local value, and each ordinary memory value are also preserved: for each such address, the scratch set does not contain it, so agreement outside the scratch set transfers the old stored value to the new memory (`WordRAM.AgreeOutside.read`). These give the frame-pointer, local, and memory hypotheses required by that result, with the state and frame pointer unchanged; it then supplies the desired relation.

**Key facts.** `Light.Compiler.Rel.of_agreeOutside`, `WordRAM.AgreeOutside.read`.
