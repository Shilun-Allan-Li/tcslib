<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.exists_padDecode_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A padded word decoding to a target

**Claim.** If Boolean words $s$ and $u$ have equal length and $B$ is greater than their common length, then there is a word of length $B$ whose padded decoding relative to $s$ is $u$.

**Proof.** Choose the word formed by appending to $u$ a true marker and then $B-|s|-1$ false entries. Its length is $|u|+1+(B-|s|-1)=B$, using $|u|=|s|$. The marker-decoding property (`Complexity.PolyHierarchy.padDecode_marker`) says that a word with this marker form decodes relative to $s$ to $u$, since $u$ and $s$ have equal length. Thus the chosen word has both required properties.

**Key facts.** `Complexity.PolyHierarchy.padDecode_marker`.
