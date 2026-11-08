<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountInc_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bounds for Binary Increment

**Claim.** For every finite Boolean word $w$, the incremented word has length at most $|w|+1$, and the number of initial consecutive true bits of $w$ is at most the length of the incremented word.

**Proof.** Proceed by induction on the word. For the empty word, incrementing produces a one-bit word, so both bounds hold. For a word $b::w$, split on its first bit. If it is false, incrementing replaces that bit by true and leaves the tail unchanged; the incremented length is therefore $1+|w|$, and the carry count is zero. If it is true, incrementing replaces that bit by false and increments the tail. The induction bounds for the tail, together with the extra leading bit, give both claimed inequalities.
