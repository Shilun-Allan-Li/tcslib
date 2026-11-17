<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.of_agreeOutside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving the storage relation

**Claim.** If the new memory agrees with the old memory outside addresses disjoint from the encoded constants and pool, and its frame pointer, locals, and ordinary memory cells have the required values, then it satisfies the storage relation for the new state and frame pointer.

**Proof.** For each address carrying an encoded constant or pool index, the disjointness hypothesis says that address is outside the set where the memories may differ. Agreement outside that set therefore gives the same value in the new memory as in the old one (`WordRAM.AgreeOutside.cell`). The old relation supplies the required encodings of $1$, $0$, $-1$, and every pool index through the dispatcher, so these four parts of the relation transfer to the new memory. The frame-pointer, local-variable, and ordinary-memory parts are exactly the hypotheses about the new memory. Together these are all the clauses of the storage relation.

**Key facts.** `WordRAM.AgreeOutside.cell`.
