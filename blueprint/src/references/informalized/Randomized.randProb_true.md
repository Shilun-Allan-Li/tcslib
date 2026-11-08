<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of the certain event

**Claim.** For every word length $m$, the always-true event has probability $1$.

**Proof.** There are $2^m$ Boolean words of length $m$ (`Randomized.card_univ_bitstrings`), and every one satisfies the always-true event. Its probability is therefore the count $2^m$ divided by the total number $2^m$, which equals $1$.

**Key facts.** `Randomized.card_univ_bitstrings`.
