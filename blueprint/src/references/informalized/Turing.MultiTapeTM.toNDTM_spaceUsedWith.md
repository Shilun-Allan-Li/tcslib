<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean :: Turing.MultiTapeTM.toNDTM_spaceUsedWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice-Independent Space Use

**Claim.** The associated nondeterministic machine’s space use under a finite choice word equals the deterministic machine’s space use through the length of that word.

**Proof.** Expand both space measures as sums over work tapes. Fix a tape. Its visited-cell set for the nondeterministic run is the image of the indices from zero through the choice-word length, sending each index $j$ to the tape-head position after running on the prefix of length $j$. Each such prefix run agrees with the deterministic run for the prefix’s length, by choice-independent run length (`toNDTM_runWith`). For every index in the indicated range, the prefix length is $j$, so the two visited-cell sets are equal. Their cardinalities agree, and summing these equal cardinalities over the tapes proves the result.

**Key facts.** `Turing.MultiTapeTM.toNDTM_runWith`.
