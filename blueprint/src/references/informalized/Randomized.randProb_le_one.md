<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Is at Most One

**Claim.** For any natural number $m$ and any predicate on finite Boolean words, the probability that a uniformly random Boolean word of length $m$ satisfies the predicate is at most $1$.

**Proof.** The satisfying words form a subset of all Boolean words of length $m$, so their number is at most the total number of such words. There are exactly $2^m$ Boolean words (`Randomized.card_univ_bitstrings`). Dividing the count of satisfying words by this total therefore gives a probability at most $1.

**Key facts.** `Randomized.card_univ_bitstrings`.
