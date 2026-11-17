<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.copiedPayload_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Copy of the Initial Input

**Claim.** For a finite deterministic machine $M$ and Boolean word $x$, the copied payload vector with count $|x|+1$ equals the head-centered payload vector of $M$'s initial configuration on $x$.

**Proof.** Compare the two vectors separately on the work lanes and the input lane. Every work lane is blank in the copied vector, and it is also blank in the source vector because the initial configuration has empty work tapes. On the input lane, the initial head position is $1$, so the head-centered coordinate $z$ addresses input coordinate $z$. The copied vector includes the input payload at coordinate $-1$ and at each coordinate from $0$ through $|x|$; with count $|x|+1$, these are exactly the coordinates on which the source input payload can be nonblank. At all other coordinates the source payload is blank by the outside-support fact (`Complexity.inputPayload_outside`), matching the copied vector. Hence the vectors agree at every lane and coordinate.

**Key facts.** `Complexity.inputPayload_outside`.
