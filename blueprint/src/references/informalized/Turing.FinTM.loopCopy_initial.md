<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopCopy_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Copying Tape

**Claim.** With empty processed prefix and remaining suffix $w$, the copying tape is the buffer tape of $w$.

**Proof.** Fix an integer cell. If it is negative, the buffer convention makes both tapes blank. If it is nonnegative, it is not below the empty prefix’s length, so the copying-tape definition returns the buffer value of the concatenation of the empty prefix and $w$, which is the buffer of $w$.
