<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.apply_workTapes_eq_of_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Cells Away From the Head

**Claim.** Applying an action to a configuration leaves the content at position $z$ on tape $i$ unchanged whenever $z$ differs from that tape's head position in the original configuration.

**Proof.** For tape $i$, the action either makes no write or updates the tape's content only at the original head position. In the no-write case the tape is unchanged everywhere. In the update case, since $z$ is not the head position, updating the tape at the head does not alter its value at $z$.
