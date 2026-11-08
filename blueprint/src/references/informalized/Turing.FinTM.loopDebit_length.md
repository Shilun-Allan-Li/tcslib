<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopDebit_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrement Preserves Length

**Claim.** For every Boolean word $u$, the fixed-width decrement operation produces a word of the same length.

**Proof.** Induct on the word. The empty word is mapped to the empty word, so the claim holds. For a word with head bit $b$ and tail $u$, split on the two possible values of $b$. If $b$ is true, decrementing changes that bit to false and leaves the tail unchanged, preserving length. If $b$ is false, the result has a true head bit followed by the recursively decremented tail. By the induction hypothesis that tail has the original tail's length, so adjoining one head bit preserves the full word's length.
