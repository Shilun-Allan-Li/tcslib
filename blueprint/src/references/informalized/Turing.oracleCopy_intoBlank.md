<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleCopy_intoBlank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Word into a Blank Tape

**Claim.** Starting in the sweep phase with the destination head at zero and its tape blank, if the source tape contains the buffer for $z$ throughout the prescribed window, then after $2|z|+2$ steps the destination tape contains $z$ and the machine is in the done phase; at every earlier time it is not in the done phase.

**Proof.** The copy-run theorem gives the machine's exact configuration after $2|z|+2$ steps and guarantees that the done phase is not reached earlier (`copyTM_run_ofCfg`). Its final tape description writes the buffer for $z$ on the destination cells in the interval from the destination head position up to, but excluding, that position plus $|z|$, leaving other cells as they were. Since the destination head starts at zero and the destination tape is blank everywhere, this description reduces to the buffer for $z$ on the destination tape: the buffer is blank beyond the word's length and at negative positions. The earlier-time conclusion is already part of the copy-run theorem.

**Key facts.** `Turing.copyTM_run_ofCfg`.
