<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.randProb_uniformSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of repeated uniform sampling

**Claim.** The probability that the repeated sampling procedure produces an output satisfying $P$ equals the number of length-$k$ tuples of block values in the prescribed range whose first value below $N$ satisfies $P$, divided by the total number of length-$k$ tuples.

**Proof.** Set $L=\mathrm{size}(N-1)$, so the random input consists of $k$ consecutive blocks of $L$ bits. The block representation formula (`Randomized.randProb_blocks_piFinset`) identifies the probability of any predicate on the decoded block values with the number of tuples in $\{0,\ldots,2^L-1\}^k$ satisfying that predicate, divided by the total number of length-$kL$ bit strings. The sampling procedure returns the first block value below $N$, or no value if none exists; this agrees with taking the first qualifying decoded block (`Randomized.sampleTries_eq_find`). Applying the block representation to the predicate that this first qualifying value satisfies $P$ gives the claimed count. Replacing the procedure by this first-qualifying-value description preserves the probability (`Randomized.randProb_congr`).

**Key facts.** `Randomized.randProb_blocks_piFinset`, `Randomized.randProb_congr`, `Randomized.sampleTries_eq_find`.
