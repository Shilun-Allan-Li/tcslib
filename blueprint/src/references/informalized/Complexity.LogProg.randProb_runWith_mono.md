<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_runWith_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Probability Is Invariant After Halting

**Claim.** If every choice word of length $T$ leads to a halted configuration, then for every $T'\ge T$ the probability of a decidable configuration property after $T'$ random steps equals its probability after $T$ random steps.

**Proof.** For each length-$T'$ choice word, compare its run with the run on its first $T$ bits. Decompose the word into that prefix followed by a suffix. The prefix run is halted by assumption, so appending the suffix does not change the configuration (`runWith_append_of_halt`). Therefore the two events agree for each word, and their probabilities are equal (`randProb_congr`). Truncating a uniform length-$T'$ choice word to its first $T$ bits has the uniform length-$T$ distribution, which identifies the truncated event's probability with the desired length-$T$ probability (`randProb_take`).

**Key facts.** `Complexity.LogProg.runWith_append_of_halt`, `Randomized.randProb_congr`, `Randomized.randProb_take`.
