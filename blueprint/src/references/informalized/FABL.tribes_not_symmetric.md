<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Examples.lean :: FABL.tribes_not_symmetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes lacks full symmetry

**Claim.** When $w,s>1$, tribes is not invariant under every permutation of its input coordinates.

**Proof.** Assume for contradiction that tribes is invariant under every coordinate permutation. Choose the first two blocks and the first two coordinates within a block, which exist since $s,w>1$. Let $p$ be the first coordinate of the first block and $q$ the first coordinate of the second block. Define an input $x$ to be $-1$ throughout the first block and $+1$ throughout all other blocks. The first block has AND value $-1$, so no block has AND value $+1$ and tribes$(x)=-1$. Now swap $p$ and $q$. In the permuted input, the first block contains a $+1$ at its first coordinate and at its second coordinate; every other block contains a $+1$ at its second coordinate. Consequently no block is all $-1$, so every block has AND value $+1$ and tribes of the permuted input is $+1$. This contradicts the assumed invariance, since the two outputs differ.
