<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.expect_partitionFunction_averageInfluence_eq_noiseSensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Average influence equals noise sensitivity

**Claim.** For $m>0$, the expected average coordinate-flip probability of the partitioned function equals the noise sensitivity of $f$ at rate $1/m$.

**Proof.** Expand the average coordinate-flip probability as an expectation over the flipped coordinate $j$, the input $w$ to the partitioned function, and the independent choices of $z$ and $\pi$. First, for fixed $\pi$ and $j$, average over $z$. The map sending $z_i$ to $z_iw_{\pi(i)}$ is a bijection of the sign cube, and under this change of variables the two partition-function inputs become an input $x$ and the result of flipping exactly those coordinates $i$ with $\pi(i)=j$. Thus the expectation over $z,w$ is the uniform probability that $f(x)$ changes under that fiber flip (`FABL.expect_partitionFunction_flip`). Reorder the finite expectations to average over $\pi$ and $j$; finite expectations commute. For each fixed $j$, averaging the fiber-flip probability over $\pi$ equals the noise sensitivity at rate $1/m$ (`FABL.expect_flipPartitionFiber_eq_noiseSensitivity`). Averaging this same value over $j$ leaves it unchanged, proving the identity. The positivity assumption on $m$ supplies the stated valid noise-rate parameter (`FABL.inverseDimension_mem_Icc`).

**Key facts.** `FABL.expect_partitionFunction_flip`, `FABL.expect_flipPartitionFiber_eq_noiseSensitivity`, `FABL.inverseDimension_mem_Icc`.
