<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCountTape_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Finite-Word Tape Conventions

**Claim.** The tape that is blank at negative cells and stores the entries of a finite Boolean word at their nonnegative indices is equal, as a function on integer cells, to the canonical buffer tape for that word.

**Proof.** Compare the two tape functions at an arbitrary integer cell $z$. If $z<0$, both conventions return blank. Otherwise $z$ is nonnegative, and both return the list entry at index $z$ converted to a natural index, or blank if that index is outside the word. Thus the functions agree at every cell.
