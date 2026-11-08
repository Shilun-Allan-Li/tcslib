<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.readBlock_eq' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read Block Equals a Word of Matching Length

**Claim.** If $beta$ has length $w$ and the sequence value at $i+j$ equals its $j$th bit for every $j<w$, then the length-$w$ block read from position $i$ is $beta$.

**Proof.** Use the given length equality to replace $w$ by $|beta|$. The hypotheses then say that the sequence agrees with $beta$ at each position used to form the read block. The result that such agreement makes the read block equal the word (`readBlock_eq`) gives the conclusion.

**Key facts.** `Complexity.TQBFHard.readBlock_eq`.
