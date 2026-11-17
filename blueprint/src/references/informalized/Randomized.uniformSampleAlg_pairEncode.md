<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.uniformSampleAlg_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform sampling algorithm correctness

**Claim.** The uniform-sampling algorithm, on the specified pair encoding, returns the encoding of the result of applying the repeated rejection sampler to the input string.

**Proof.** The algorithm uses blocks of length given by the binary size of the target bound minus one. First, the binary subtraction performed on the encoded input has exactly that length: the value of the encoding of $w$ is $N$, and the length of the binary expansion of $N-1$ is $\operatorname{size}(N-1)$. The pair-encoding projections recover the intended control string and random string (`Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`). The loop identity for pair-encoded states (`Complexity.BinArith.forLoop_pairEncode`) reduces its iterations to the number of control bits, namely the $k$ copies of $1$. Iterating the sampling step this many times consumes the first $k$ blocks of the stated length and retains the first successful sample, if any (`Randomized.iterate_sampleStep`). With the block length identified above, this is exactly `uniformSample`; the final encoding is therefore `encSample` of that result.

**Key facts.** `Complexity.BinArith.forLoop_pairEncode`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.iterate_sampleStep`.
