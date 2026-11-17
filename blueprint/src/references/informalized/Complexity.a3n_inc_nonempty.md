<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_inc_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Increment Output

**Claim.** Whenever the fixed-width binary increment of a finite Boolean word is defined, its output is nonempty.

**Proof.** If the word is empty, its increment is undefined, so it cannot equal the empty word as a defined result. If the word is nonempty, split off its first bit. When that bit is false, increment returns a word beginning with true, which is nonempty. When the first bit is true, either incrementing the tail is undefined, or it returns some word; in the latter case the full result is obtained by adjoining false to that word and is therefore nonempty.
