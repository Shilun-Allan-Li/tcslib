<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFlag_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing the Flag Tape

**Claim.** For either optional Boolean flag value, writing blank at cell zero on the tape that stores the flag there and is blank elsewhere produces the blank tape.

**Proof.** Compare the two tapes at an arbitrary cell $z$. If $z=0$, the update writes blank there. If $z\ne0$, the update leaves the tape unchanged, and that cell was already blank. Thus every cell contains blank, which is exactly the blank tape.
