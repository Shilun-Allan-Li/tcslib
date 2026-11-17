<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unbiased and Uniform Probability

**Claim.** For every nonnegative integer $m$ and predicate $A$ on Boolean strings, biased probability with parameter $1/2$ equals the fraction of strings of length $m$ satisfying $A$.

**Proof.** Induct on $m$, allowing the predicate to vary. At length zero, there is only the empty string. If it satisfies $A$, the event agrees on the unique length-zero string with the certain event; otherwise it agrees with the impossible event. The uniform probabilities of these events are respectively $1$ and $0$ (`Randomized.randProb_congr`, `Randomized.randProb_true`, and `Randomized.randProb_false`), matching the defining values of biased probability. For the inductive step, split both probabilities according to whether the first bit is true or false. Uniform probability averages the two conditional probabilities (`Randomized.randProb_succ`); biased probability with parameter $1/2$ gives each branch weight $1/2$ (`Randomized.biasedProb_succ`). Apply the induction hypothesis to the two predicates obtained by prefixing each possible first bit. The resulting expressions agree by arithmetic.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_true`, `Randomized.randProb_false`, `Randomized.randProb_succ`, `Randomized.biasedProb_succ`.
