<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.sScan_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blockwise Decomposition of a Paired Scan

**Claim.** When both Boolean words have length $W_Nm$, scanning their paired bits one at a time and applying the two update rules yields the same pair of scan states as folding those rules over the paired decoded blocks of length $W_N$.

**Proof.** Cut each word into its $m$ consecutive blocks of length $W_N$. The reconstruction fact `eq_flatten_blocks` says that a word whose length is $W_Nm$ is the flattening of these blocks. Because corresponding blocks have equal length, `zip_flatten` identifies the bitwise zip of the original words with the flattening of the list of zipped block pairs.

The scan uses a buffer of $W_N$ bit-pairs. The fold lemma `foldl_adStep_flatten` says that processing a concatenation of full buffer-sized chunks updates the scan state once per chunk, with the buffer reset at each boundary. Here each zipped block pair has exactly $W_N$ bit-pairs, so the resulting scan state is the fold of the block update $sChunk$ over the zipped blocks. Applying `foldl_pair` separates this paired fold into its two components. Finally, the paired update $sChunk$ applies `pairChunk` to each block pair, while `blocksD` decodes each individual block; by the definitions these give exactly the paired lists of decoded blocks. Substituting this identification yields the claimed two folds.

**Key facts.** `Complexity.Codec.eq_flatten_blocks`, `Complexity.Codec.zip_flatten`, `Complexity.Codec.foldl_adStep_flatten`, `Complexity.Codec.foldl_pair`.
