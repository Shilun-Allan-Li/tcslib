<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.uniformSample_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform sampling specification

**Claim.** For $N\ge1$ and $\delta>0$, the repeated rejection sampler has the stated polynomial-time implementation, returns only values below $N$, gives equal probability to every such value conditional on success, and fails with probability at most $\delta$ for the specified number of trials.

**Proof.** Set $k=\lceil\log_2\lceil\delta^{-1}\rceil\rceil$. The algorithm is polynomial-time by the established complexity bound (`Randomized.polyTimeComputable_uniformSampleAlg`). Its behavior on the prescribed input follows from the algorithm’s correctness for pair encodings (`Randomized.uniformSampleAlg_pairEncode`) and the fact that decoding the binary representation of $N$ recovers $N$ (`Complexity.LogProg.bitsVal_bits`). Any returned sample is less than $N$ (`Randomized.lt_of_uniformSample_eq_some`), and for each $i<N$, its probability multiplied by $N$ equals one minus the probability of failure (`Randomized.randProb_uniformSample_some_mul`).

For the failure estimate, the rejection bound gives failure probability at most $(1/2)^k$ (`Randomized.randProb_uniformSample_none_le`). By the definition of $k$ and the ceiling bounds, $\delta^{-1}\le \lceil\delta^{-1}\rceil\le 2^k$. Since $\delta>0$, taking reciprocals reverses this inequality and yields $(2^k)^{-1}\le\delta$. Hence the failure probability is at most $\delta$.

**Key facts.** `Randomized.polyTimeComputable_uniformSampleAlg`, `Randomized.uniformSampleAlg_pairEncode`, `Complexity.LogProg.bitsVal_bits`, `Randomized.lt_of_uniformSample_eq_some`, `Randomized.randProb_uniformSample_some_mul`, `Randomized.randProb_uniformSample_none_le`.
