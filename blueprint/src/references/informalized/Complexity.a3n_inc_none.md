<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_inc_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Increment Overflow Characterization

**Claim.** A fixed-width increment of a finite Boolean word is undefined exactly when the word consists entirely of true bits, including the empty word.

**Proof.** Induct on the word. For the empty word, the increment is undefined by its defining clause, and the empty word is the replication of true bits zero times. For a word with first bit false, increment is defined and simply changes that bit to true, so the left side is false; the word cannot be all true, so the right side is false as well. For a word with first bit true, the increment is undefined exactly when incrementing the tail is undefined, since the recursive result is mapped by adjoining a false bit. By the induction hypothesis, this happens exactly when the tail consists entirely of true bits. The whole word then consists entirely of true bits, which is exactly its being the replication of true bits at its length.
