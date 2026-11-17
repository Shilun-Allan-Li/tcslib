<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Constant Predicate

**Claim.** For any natural number $n$ and decidable proposition $p$, the probability that a uniformly random Boolean word of length $n$ satisfies the constant predicate $p$ is $1$ if $p$ holds and $0$ otherwise.

**Proof.** Split into the two cases $p$ and $\neg p$. If $p$ holds, the constant predicate agrees on every word with the constantly true predicate, so its probability equals $1$ by the fact that the constantly true predicate has probability one (`Randomized.randProb_true`). If $p$ fails, the constant predicate agrees on every word with the constantly false predicate, whose probability is zero (`Randomized.randProb_false`). These are exactly the two values specified by the conditional expression.

**Key facts.** `Randomized.randProb_true`, `Randomized.randProb_false`, `Randomized.randProb_congr`.
