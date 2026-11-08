<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRow_stored -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Row Construction

**Claim.** There is a time at most $l(3W+4)$ when the row controller, started at field index and copier control zero, reaches field index $l$ in copier start control with the record extended by the stored encodings of all $l$ counter words.

**Proof.** Apply the bounded-prefix result (`clRow_prefix_run`) with $j=l$. Its time bound becomes $l(3W+4)$, and its terminal configuration has field index $l$, copier control $0$, and record equal to the initial record followed by the stored prefix of length $l$.

**Key facts.** `Complexity.clRow_prefix_run`.
