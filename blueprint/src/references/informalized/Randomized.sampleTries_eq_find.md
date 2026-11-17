<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.sampleTries_eq_find -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Sampling as List Search

**Claim.** Sampling at most $k$ successive length-$L$ blocks and returning the first block value below $N$ gives the same result as searching the list of the first $k$ block values for its first value below $N$.

**Proof.** Induct on the number $k$ of allowed samples, generalizing over the bit list. At $k=0$, both procedures return no value. For the successor case, the first sampled value is the value of the first length-$L$ block. The remaining block values are exactly those obtained by applying the same block-value construction to the list after dropping its first $L$ bits: dropping the first block and then the next $j$ blocks is the same as dropping $(j+1)L$ bits. Thus both procedures first test the same value against $N$. If it is below $N$, both return it; otherwise, both continue on the remaining blocks, where the induction hypothesis identifies their results.
