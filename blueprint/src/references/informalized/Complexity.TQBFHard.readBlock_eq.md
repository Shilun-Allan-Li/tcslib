<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.readBlock_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read Block Equals a Prescribed Word

**Claim.** If the sequence value at $i+j$ is the $j$th bit of a finite word $\beta$ for each $j<|\beta|$, then the block of that length read from position $i$ equals $\beta$.

**Proof.** Both lists have length $|\beta|$. To prove they are equal, compare entries at an arbitrary index $j$ in that range. The read block's entry is the sequence value at $i+j$; by hypothesis this is the default-safe lookup of $\beta$ at $j$, which, since $j<|\beta|$, is exactly its $j$th entry. Hence the lists agree at every index and are equal.
