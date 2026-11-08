<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropIdx_prefix_address -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Address Under Index Dropping

**Claim.** For $j<2|w|+2$, the bit at index $j$ after dropping the index equals the bit at index $4j$ in the larger encoding, with out-of-range lookups defaulting to $0$.

**Proof.** First examine the larger encoding at index $4j$. Since $j<2|w|+2$, this index lies in the doubled prefix whose entries encode the nested string; the pair-encoding lookup formula reduces it to index $2j$ of the nested string. The same formula, using the corresponding length bound, reduces that lookup to index $j$ of the encoding of $w,b$. On the other hand, dropping the index from the nested encoding yields the encoding of $w,b'$. Applying the lookup formula to this result at index $j$ gives the same bit as the encoding of $w,b$: the relevant prefix positions depend only on $w$, and the delimiter positions agree. The bounds ensure that the suffix cannot affect this lookup, including when lookups are interpreted with default value $0$.

**Key facts.** `Complexity.pairEncode_getD`, `Complexity.dropIdx_pairEncode`, `Turing.length_pairEncode`.
