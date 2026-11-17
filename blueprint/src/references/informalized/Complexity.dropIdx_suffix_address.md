<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropIdx_suffix_address -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix Address Under Index Dropping

**Claim.** For $j<|b'|$, the lookup at index $2|w|+2+j$ after dropping the index equals the lookup at index $4|\langle w,b\rangle|+4+2j$ in the larger encoding, with default value $0$ for out-of-range lookups.

**Proof.** The larger encoding's lookup formula places the specified index in the suffix following its doubled prefix and delimiter: it reduces the lookup to index $2|\langle w,b\rangle|+2+j$ of the nested encoding. Dropping the index gives the encoding of $w,b'$. At index $2|w|+2+j$, the lookup formula places the position in its suffix, and reduces it to index $j$ of $b'$. Applying the formula to the nested encoding at index $2|\langle w,b\rangle|+2+j$ likewise reaches index $j$ of $b'$. The hypothesis $j<|b'|$ ensures these are genuine suffix positions. The pair-encoding length formula supplies the length identities used to verify the prefix and delimiter bounds.

**Key facts.** `Complexity.pairEncode_getD`, `Complexity.dropIdx_pairEncode`, `Turing.length_pairEncode`.
