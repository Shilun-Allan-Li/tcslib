<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/InnerProductModTwo.lean :: FABL.innerProductModTwoBoolean_ne_one_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonconstancy of the Inner Product Function

**Claim.** For every positive natural number $n$, the Boolean function that sign-encodes the inner product modulo two on the sign cube of dimension $2n$ is not constantly $1$.

**Proof.** Choose a coordinate $i$ in the length-$n$ block, possible because $n>0$, and let $e$ be the vector supported at $i$ with value $1$. Its inner product with itself is $1$, since the only nonzero summand is $e_i e_i=1$. Evaluate the function at the sign encoding of the concatenation of $e$ with itself. The block-encoding identity (\texttt{innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks}) says this value is the sign encoding of $1$, namely $-1$. If the function were constantly $1$, its value there would also be $1$, a contradiction.

**Key facts.** `FABL.innerProductModTwoBoolean_binaryCubeSignEquiv_joinF₂CubeBlocks`.
