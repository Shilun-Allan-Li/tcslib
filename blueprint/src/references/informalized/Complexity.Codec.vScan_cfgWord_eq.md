<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.vScan_cfgWord_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning Encoded Configuration Blocks

**Claim.** For a configuration encoded with radius $s$, scanning the prefix containing its $2s+1$ cell blocks yields the same verifier state as folding the cell verifier step over cells $0$ through $2s$, starting from the initial state.

**Proof.** Apply the fixed-width block description of scanning (`vScan_eq`) to the prefix, whose length is exactly $W(2s+1)$ by the configuration-word length formula. For each block index $j<2s+1$, the corresponding width-$W$ slice of this prefix is the $j$th block of the encoded configuration: the prefix is precisely the concatenation of the cell chunks (`cfgWord_take`), and the block extraction property for `chunksWord` (`block_chunksWord`) identifies that slice with the encoding of `cellOf s C j`. Decoding this encoded chunk therefore returns that cell. Thus the list of decoded blocks in the scan formula is exactly the list of cells, each wrapped in `some`. Finally, folding the option-valued step over present cells is the same as folding the ordinary verifier step (`foldl_vStepO_some`), giving the claimed equality.

**Key facts.** `Complexity.Codec.vScan_eq`, `Complexity.Codec.cfgWord_take`, `Complexity.Codec.block_chunksWord`, `Complexity.Codec.foldl_vStepO_some`.
