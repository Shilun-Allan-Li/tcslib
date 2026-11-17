<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clGroups_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization of the clause-group list

**Claim.** Concatenating the round chunks for indices $0$ through $R$, where $R=n+(k+3)T+k+1$, with the formula terminator appended precisely at index $R$, gives the serialization of the flattened clause-group list.

**Proof.** The chunk-serialization identity (`clChunks_serialize`) says that concatenating chunks over a range of indices serializes the list obtained by flattening the corresponding groups. Apply it to the indexed groups drawn from the clause-group list. The length computation (`clGroups_length`) identifies the range endpoint $R+1$ with the length of that list, while indexed reconstruction (`clGroups_index`) identifies the list of groups retrieved over this full range with the original clause-group list. Flattening therefore gives exactly the flattened group list in the claim, and the chunk concatenation is its serialization.

**Key facts.** `Complexity.clChunks_serialize`, `Complexity.clGroups_length`, `Complexity.clGroups_index`.
