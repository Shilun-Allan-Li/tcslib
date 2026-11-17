<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.nandPair_two_levels_eq_tribes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-level NAND realizes tribes

**Claim.** For every four-coordinate input, applying NAND to each coordinate pair and then NAND to the two outputs gives the tribes function with two blocks of width two.

**Proof.** Write the input as two pairs $(a,b)$ and $(c,d)$. The inner NAND on $(a,b)$ is $1$ exactly when $a=b=-1$; otherwise it is $-1$. The outer NAND is $1$ exactly when both inner outputs are $-1$, which is equivalent to each pair containing at least one $1$. This is precisely the stated tribes condition. The proof checks the possible signs of the four coordinates, and the coordinate reindexing identifies the two pairs with the two blocks.
