<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.tribes_blockCoordinatePermutation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Invariance Under Block and Within-Block Permutations

**Claim.** For any permutations of the blocks and of the coordinates within each block, permuting the input accordingly does not change the value of the tribes function.

**Proof.** After applying the input permutation, the block indexed by $i$ is exactly the original block indexed by the permuted block index, with its coordinates permuted by the within-block permutation. This follows coordinate by coordinate from the definition of the block-coordinate permutation. Since AND is symmetric, permuting the coordinates within a block does not change that block's AND value (`andFunction_symmetric`). Consequently, the list of block outputs is just the original list permuted by the block permutation. Since OR is symmetric, that permutation leaves the final output unchanged (`orFunction_symmetric`).

**Key facts.** `FABL.andFunction_symmetric`, `FABL.orFunction_symmetric`.
