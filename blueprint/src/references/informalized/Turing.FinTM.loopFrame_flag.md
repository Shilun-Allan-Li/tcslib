<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFrame_flag -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flag Track Reads at the Origin

**Claim.** In the controller frame, the symbol scanned on the flag track is the value of the flag tape at cell $0$.

**Proof.** The flag track has index equal to the number of the body machine's work tapes. By the definition of the frame, this track is assigned the flag tape and its head is placed at $0$. The scanned symbol is therefore the flag tape's value at $0$.
