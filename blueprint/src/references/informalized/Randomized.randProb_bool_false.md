<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_bool_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Boolean Output Probabilities

**Claim.** The probability that $B$ returns false on a uniform Boolean word of length $m$ is one minus the probability that it returns true.

**Proof.** On Boolean outputs, returning false is equivalent to not returning true. Thus, on every word of length $m$, the false-output predicate agrees with the complement of the true-output predicate; agreement on all such words preserves probability (`Randomized.randProb_congr`). The probability of a complementary event is one minus the probability of the event (`Randomized.randProb_not`), giving the formula.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_not`.
