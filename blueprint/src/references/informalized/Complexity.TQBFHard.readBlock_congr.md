<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.readBlock_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Determines a Read Block

**Claim.** If two bit sequences agree at every position from $i$ through $i+w-1$, then the length-$w$ blocks read from position $i$ in the two sequences are equal.

**Proof.** A read block is the finite list whose entry at each index $j<w$ is the sequence value at $i+j$. The hypothesis gives equality of these values for every such index. Thus the two functions on the finite index set defining the lists agree pointwise, so their lists are equal.
