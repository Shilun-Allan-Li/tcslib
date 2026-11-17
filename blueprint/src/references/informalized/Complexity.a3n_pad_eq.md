<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_pad_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# All-Ones Word Characterization

**Claim.** A Boolean word consists entirely of ones and has length $n$ exactly when it is the all-ones word of length $n$.

**Proof.** For the forward direction, replace the word's length by $n$ in its given expression as a replication of true bits. Conversely, if the word is the replication of true bits $n$ times, its length is $n$ and it is also the replication of true bits at its own length, so both stated properties hold.
