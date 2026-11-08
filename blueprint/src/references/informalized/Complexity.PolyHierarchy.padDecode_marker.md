<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.padDecode_marker -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marked padded-word decoding

**Claim.** If $u$ and $s$ have equal lengths, then decoding $u$ followed by a true marker and any number of false bits, relative to $s$, returns $u$.

**Proof.** The marker lemma says that splitting this padded word at its last true bit returns exactly $u$ (`Complexity.PolyHierarchy.splitAtLastTrue_marker`). The decoder therefore selects this prefix, and the length condition holds by hypothesis. Its output is consequently $u$.

**Key facts.** `Complexity.PolyHierarchy.splitAtLastTrue_marker`.
