<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Debit_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement Preserves Width

**Claim.** For every Boolean word $u$, the fixed-width decrement of $u$ has the same length as $u$.

**Proof.** Induct on $u$. The empty word decrements to the empty word. For a word with leading bit $1$, decrement changes that bit to $0$ and leaves the tail unchanged, preserving length. For a leading $0$, it changes that bit to $1$ and recursively decrements the tail; the induction hypothesis says the tail's length is preserved, hence so is the whole word's length.
