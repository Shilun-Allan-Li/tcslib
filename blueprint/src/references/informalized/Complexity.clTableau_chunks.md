<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTableau_chunks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chunked Serialization of the Tableau

**Claim.** Concatenating the serialized clause groups in order, with a false terminator exactly on the final round, produces the serialization of the flattened tableau formula.

**Proof.** Instantiate the general serialization theorem for ordered clause groups (`Complexity.clGroups_serialize`) with the tableau's pin, initial, state, input, work-tape, and acceptance groups. Its round bound is the last round determined by the input length, number of work tapes, and time bound. The tableau's group list is exactly this instance of the general group construction, and its flattened formula is the tableau formula. The theorem therefore identifies the concatenation of the per-round chunks, including the single final terminator, with the serialization of that formula.

**Key facts.** `Complexity.clGroups_serialize`.
