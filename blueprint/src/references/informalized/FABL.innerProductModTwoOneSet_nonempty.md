<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/InnerProductSupportDensity.lean :: FABL.innerProductModTwoOneSet_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Support of the Inner Product

**Claim.** For every positive natural number $m$, some vector in $\mathbb{F}_2^{2m}$ has inner product modulo two equal to $1$ between its two consecutive length-$m$ blocks.

**Proof.** Choose a coordinate $i$ in the length-$m$ block and let $e$ be the vector supported at $i$ with value $1$. Concatenate $e$ with itself. The block decomposition identity (\texttt{innerProductModTwoBit_joinF₂CubeBlocks}) identifies the inner product bit of this concatenation with $e\cdot e$. In the dot product, only coordinate $i$ contributes, and that contribution is $1$. Hence the concatenation belongs to the specified support, proving it is nonempty.

**Key facts.** `FABL.innerProductModTwoBit_joinF₂CubeBlocks`.
