<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.recursiveMajority_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Majority Successor Rule

**Claim.** For natural numbers $n,d$ and a sign vector $x$ with $n^{d+1}$ coordinates, recursive majority of depth $d+1$ is majority of the $n$ recursive-majority outputs obtained from the $n$ consecutive blocks of $n^d$ coordinates of $x$.

**Proof.** This is exactly the successor clause in the recursive definition: at depth $d+1$, form the $n$ blocks of depth-$d$ inputs, apply recursive majority of depth $d$ to each block, and take ordinary majority of those outputs.
