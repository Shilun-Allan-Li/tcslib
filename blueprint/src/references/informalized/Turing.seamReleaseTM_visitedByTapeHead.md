<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamReleaseTM_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape-Head Visits Under Seam Release

**Claim.** Starting from the anchor configuration renamed into the left summand, the seam-release machine and the original machine visit exactly the same work-tape head positions through any given time.

**Proof.** Unfold the visited-position sets: each is the image of the time interval from $0$ through $t$ under the function that records the chosen tape’s head position. It is therefore enough to show that these position functions agree at every time in that interval. At time $0$, both configurations are the given starting configuration up to state renaming, which does not change head positions. For any positive time $s$, the iterate identity for seam release says that the seam-release configuration at time $s$ is the original machine’s configuration at time $s$, with its state mapped into the right summand (`seamReleaseTM_runFrom_pos`). State renaming leaves the head position unchanged. Hence the two image functions agree at every time, so their image sets are equal.

**Key facts.** `Turing.seamReleaseTM_runFrom_pos`.
