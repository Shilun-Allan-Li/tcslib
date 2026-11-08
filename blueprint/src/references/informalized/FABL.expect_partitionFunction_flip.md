<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.expect_partitionFunction_flip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partition-function flip identity

**Claim.** For fixed $f,\pi,w,j$, the uniform probability over $z$ that the partition function changes when coordinate $j$ of $w$ is flipped equals the uniform probability over $x$ that $f(x)$ changes when all coordinates in the fiber $\{i:\pi(i)=j\}$ are flipped.

**Proof.** Fix $w$ and define $x_i=z_iw_{\pi(i)}$. Multiplication by the fixed signs $w_{\pi(i)}$ is a bijection of the sign cube, so uniform averaging over $z$ is equivalent to uniform averaging over $x$. By definition, the partition function at $w$ is $f(x)$. Flipping coordinate $j$ of $w$ changes the input coordinate $x_i$ precisely when $\pi(i)=j$, replacing that sign by its negative; coordinates outside this fiber are unchanged. Hence the two events being averaged agree under the bijection, and their uniform probabilities are equal.
