<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_narun_mono_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Probability Is Length Invariant After Halting

**Claim.** If all length-$N$ choice words halt from the initial configuration, then for every $N'\ge N$ the probability of any decidable configuration property after $N'$ bits equals its probability after $N$ bits.

**Proof.** For each length-$N'$ choice word, replace the event of interest by the same event evaluated on its first $N$ bits. To justify this replacement, split the word into its length-$N$ prefix and its remaining suffix. The run on the prefix has halted by assumption, and a halted run is unchanged by any further choices (`narun_append_of_halted`). Thus these two events agree for every word, and their probabilities agree (`randProb_congr`). Finally, truncating a uniformly random length-$N'$ word to its first $N$ bits gives the uniform length-$N$ distribution, so the truncated event has the length-$N$ probability (`randProb_take`).

**Key facts.** `Complexity.LogProg.narun_append_of_halted`, `Randomized.randProb_congr`, `Randomized.randProb_take`.
