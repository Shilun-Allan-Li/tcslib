<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.recursiveMajority_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-One Recursive Majority

**Claim.** For every $n$ and every sign input $x$ indexed by $n^1$ coordinates, depth-one recursive majority equals ordinary $n$-input majority applied to the signs of $x$ at the corresponding coordinates.

**Proof.** Expand depth-one recursive majority by its successor equation and expand depth-zero recursive majority (`recursiveMajority_succ`, `recursiveMajority_zero`). The result is majority applied to the values of the depth-zero function on each one-coordinate block. Such a block's sole coordinate is the original input coordinate indexed by the corresponding pair $(i,0)$ under the canonical product indexing. At depth one this index is exactly the cast of $i$ into the coordinate type of $x$, so the branch value is $x$ at that coordinate. Substituting these branch values gives the claimed formula.

**Key facts.** `FABL.recursiveMajority_succ`, `FABL.recursiveMajority_zero`.
