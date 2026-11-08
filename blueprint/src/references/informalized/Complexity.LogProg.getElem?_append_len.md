<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean :: Complexity.LogProg.getElem?_append_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexing an Appended List

**Claim.** For finite Boolean words $pre$ and $rest$ and any natural number $k$, the possibly undefined entry of $pre++rest$ at index $|pre|+k$ equals the possibly undefined entry of $rest$ at index $k$.

**Proof.** The index $|pre|+k$ lies at or beyond the end of the initial list $pre$. The list-indexing rule for an appended list therefore identifies the entry there with the entry of the second list at index $(|pre|+k)-|pre|$. This index simplifies to $k$, giving the claimed equality, including when that entry is undefined.
