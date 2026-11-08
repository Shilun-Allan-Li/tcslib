<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.randProb_uniformSample_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal probabilities for accepted outputs

**Claim.** When $i<N$ and $j<N$, the repeated sampling procedure returns $i$ and $j$ with equal probabilities.

**Proof.** Let $L=\mathrm{size}(N-1)$. The size bound `Randomized.le_two_pow_size_pred` ensures that both accepted values lie in the range of possible decoded length-$L$ blocks. By the counting formula for repeated sampling (`Randomized.randProb_uniformSample`), each output probability is proportional to the number of length-$k$ block tuples whose first entry below $N$ is that output. Consider the permutation that swaps $i$ and $j$ in every block value. It preserves the set of allowed block values, and it preserves whether a value is below $N$, because both swapped values are below $N$ and all other values are fixed. Applying the swap coordinatewise gives a bijection on allowed tuples. It carries the first block value below $N$ to its swapped value, so tuples whose first accepted value is $i$ correspond exactly to those whose first accepted value is $j$. The two counts, and hence the probabilities with their common denominator, are equal.

**Key facts.** `Randomized.le_two_pow_size_pred`, `Randomized.randProb_uniformSample`.
