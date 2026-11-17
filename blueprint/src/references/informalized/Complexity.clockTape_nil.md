<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.clockTape_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Tape of the Empty Word

**Claim.** The captured clock tape of the empty word has the origin marker at coordinate $0$ and is blank at every other integer coordinate.

**Proof.** Evaluate both sides at an arbitrary integer $z$. At $z=0$, the clock tape gives the origin marker, and the function update also gives the origin marker there. At every other coordinate, the clock tape's buffer is blank because the word is empty, while the update leaves the everywhere-blank function unchanged. Hence the two functions agree at every coordinate.
