<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.dblAt_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization by the Doubled Pair Encoding

**Claim.** The doubled encoding of $u$ in $x$ starting at $q$ holds exactly when the suffix of $x$ from $q$ is the pair encoding of $u$ followed by the suffix from $q+2|u|+2$.

**Proof.** For the forward implication, the delimiter’s final bit is true, so the position immediately after the encoded block lies within $x$. Compare the two suffixes by their lengths and entries, using that a list is determined by its length and indexed entries. At an offset $i$ within the doubled data block, write $i$ as either $2j$ or $2j+1$; the defining conditions for the doubled encoding identify the corresponding entry with the $j$th bit of $u$. At the next two offsets the delimiter conditions give $0$ and $1$. Beyond the delimiter, the pair encoding reads from the remaining suffix, and the drop-index identity shows these entries agree as well. For the reverse implication, equality of the two suffixes identifies every entry of $x$ at position $q+j$ with the pair encoding’s entry at offset $j$. The pair encoding’s entry formula then gives both copies of each bit of $u$ and the two delimiter bits, which are precisely the conditions defining the doubled encoding.

**Key facts.** `Complexity.lt_of_getD_true`, `Complexity.ext_getD'`, `Complexity.getD_drop`, `Complexity.pairEncode_getD`, `Turing.length_pairEncode`.
