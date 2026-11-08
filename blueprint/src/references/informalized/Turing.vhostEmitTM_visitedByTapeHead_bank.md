<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostEmitTM_visitedByTapeHead_bank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Cells on Embedded Work Tapes

**Claim.** For each bank tape, the virtual-host machine visits exactly the cells visited by the corresponding work-tape head of $M$ through time $t$.

**Proof.** Unfold the visited-cell sets: each is the image of the times $0,1,\ldots,t$ under the corresponding head-position function. For an arbitrary such time $u$, the run-correspondence theorem (`Turing.vhostEmitTM_runFrom`) identifies the virtual-host configuration with the encoding of $M$'s configuration at time $u$, for some valid tag. By the definition of the encoding, the head position on bank tape $i$ is exactly the head position on work tape $i$ of $M$. Thus the two position functions agree at every time in the range, and so their image sets are equal.

**Key facts.** `Turing.vhostEmitTM_runFrom`.
