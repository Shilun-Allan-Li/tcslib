<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Formula for a Word

**Claim.** For every finite Boolean word, its probability under the recursively defined biased word measure is the product of the weights of its bits, with weight $\rho$ for true and $1-\rho$ for false.

**Proof.** Proceed by induction on the word. For the empty word, the defining probability is $1$, matching the empty product. For a word $b::u$, expand the probability by the first-bit recurrence (\texttt{Randomized.biasedProb_succ}). If $b$ is false, the event that a prefixed true bit equals $b::u$ is impossible, while the event for a prefixed false bit is exactly that the remaining word equals $u$. These event replacements preserve the probabilities by invariance under length-indexed event equivalence (\texttt{Randomized.biasedProb_congr}). The induction hypothesis then gives the product for $u$, multiplied by the false-bit weight $1-\rho$. If $b$ is true, the true-prefixed event reduces to equality with $u$ and the false-prefixed event is impossible; the same recurrence, event invariance, and induction hypothesis give the product with the additional factor $\rho$.

**Key facts.** `Randomized.biasedProb_succ`, `Randomized.biasedProb_congr`.
