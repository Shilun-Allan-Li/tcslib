<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.randProb_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of an Impossible Event

**Claim.** For any verifier model and natural number $m$, an always-false condition has probability zero on a uniformly random Boolean word of length $m$.

**Proof.** By definition, this probability is the cardinality of the set of length-$m$ Boolean words satisfying the condition, divided by $2^m$. Since the condition is false for every word, that set is empty and has cardinality zero; thus the quotient is zero.
