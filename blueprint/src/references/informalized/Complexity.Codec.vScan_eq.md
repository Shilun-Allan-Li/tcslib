<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.vScan_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning Fixed-Width Blocks

**Claim.** If a Boolean word $u$ has length $Wm$, then scanning it gives the state obtained by applying the option-valued verifier step successively to the decoded width-$W$ blocks of $u$, indexed from $0$ to $m-1$.

**Proof.** First express $u$ as the concatenation of its consecutive width-$W$ blocks, using `eq_flatten_blocks`. Each block has length $W$: the index bound $j<m$, together with $|u|=Wm$, ensures the slice from position $Wj$ through the next $W$ positions is within the word. Pairing each bit of $u$ with itself then agrees with concatenating the pairwise zips of corresponding blocks (`zip_flatten`). The scanner processes these paired bits with an accumulator whose buffer has width $W$; the accumulator flattening property (`foldl_adStep_flatten`) says that processing the concatenation of complete blocks applies the block operation to each block in turn, leaving the buffer reset at the boundary. Within each block, the two entries of every pair are identical, so projecting the first coordinate recovers the original block. Rewriting the blocks as the range-indexed slices, and expressing the finite-index list as a mapped range (`ofFn_eq_map_range`), yields exactly the stated fold of decoded blocks.

**Key facts.** `Complexity.Codec.eq_flatten_blocks`, `Complexity.Codec.zip_flatten`, `Complexity.Codec.foldl_adStep_flatten`, `Complexity.Codec.ofFn_eq_map_range`.
