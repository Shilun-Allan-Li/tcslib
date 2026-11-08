<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFrame_counter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Track Reads Its Specified Cell

**Claim.** In the controller frame, the symbol scanned on the counter track is the value of the counter tape at the counter head position $c$.

**Proof.** The counter track has index one greater than the number of the body machine's work tapes. By the definition of the frame, the tape at that index is the counter tape, and its head position is $c$. A scanned symbol is the tape's value at its head position, so it is the counter tape's value at $c$.
