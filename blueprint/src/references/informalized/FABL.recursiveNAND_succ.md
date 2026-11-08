<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNAND_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND Step

**Claim.** For every natural number $d$ and every sign vector $x$ with $2^{d+1}$ coordinates, the recursive NAND of depth $d+1$ is the NAND of the two recursive NAND outputs obtained from the two blocks of $2^d$ coordinates of $x$.

**Proof.** This is exactly the successor clause in the recursive definition: at depth $d+1$, the function applies NAND to the depth-$d$ recursive NANDs of the two input blocks. Thus the two sides agree by unfolding that definition.
