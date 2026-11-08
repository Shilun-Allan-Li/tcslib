<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clGroups_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed reconstruction of a list

**Claim.** For every list $G$ of conjunctive normal form formulas, mapping the indices from $0$ through $|G|-1$ to their corresponding entries of $G$, using the empty formula as the default for an out-of-range lookup, reconstructs $G$.

**Proof.** The mapped list has the same length as $G$, since it maps one entry for each index in the range. To prove the lists equal, compare their entries at an arbitrary index within this common length. The index lies in the range used for the map, and its lookup in $G$ is in bounds; hence the optional lookup is exactly the corresponding entry of $G$, so applying the default has no effect. Thus the two lists agree at every valid index and have equal lengths, which establishes equality by extensionality of lists.
