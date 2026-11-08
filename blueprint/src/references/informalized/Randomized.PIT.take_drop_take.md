<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroP.lean :: Randomized.PIT.take_drop_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking After Dropping from a Truncation

**Claim.** If $a+b\le N$, taking $b$ entries after dropping $a$ entries from the first $N$ entries of $l$ gives the same list as taking $b$ entries after dropping $a$ entries directly from $l$.

**Proof.** Dropping $a$ entries from the first $N$ entries of a list is the same as first dropping $a$ entries from the list and then taking $N-a$ entries. Taking a further $b$ entries therefore amounts to taking $\min(b,N-a)$ entries from the list after the initial drop. The hypothesis $a+b\le N$ gives $b\le N-a$, so this minimum is $b$, as required.
