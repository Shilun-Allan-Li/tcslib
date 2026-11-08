<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.capture_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capture Tape Visitation and Space

**Claim.** Under the transition-agreement hypothesis and the assumption that the original machine remains active before time $t$, the first $k$ captured tapes have the same visited head positions and space usage as the original tapes, while the additional tape uses at most the increase in output length plus one.

**Proof.** For every time $u\le t$, the nonhalting hypothesis applies at each earlier time in the run up to $u$. The lockstep run theorem therefore identifies the host configuration at time $u$ with the capture of the original configuration at that time (`Turing.capture_run`). On each of the first $k$ tapes, the captured head position is the original head position. Applying this pointwise equality to the set of times from zero through $t$ shows that the visited-position sets agree; taking their cardinalities gives equality of space usage.

For the additional tape, its head at time $u$ is at position $|pre|+|output_u|$, where $output_u$ is the original output at time $u$. Output is a prefix of every later output (`Turing.MultiTapeTM.output_prefix`), so its length is nondecreasing, and at time zero it is the initial output (`Turing.MultiTapeTM.runFrom_zero`). Consequently all visited positions lie in the integer interval from $|pre|+|output_0|$ to $|pre|+|output_t|$. This interval has $|output_t|-|output_0|+1$ integer positions, yielding the claimed upper bound on the additional tape's space.

**Key facts.** `Turing.capture_run`, `Turing.MultiTapeTM.output_prefix`, `Turing.MultiTapeTM.runFrom_zero`.
