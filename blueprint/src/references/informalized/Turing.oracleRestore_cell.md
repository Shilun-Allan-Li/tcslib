<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleRestore_cell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration at the Bookmarked Cell

**Claim.** Two steps from the ready configuration containing the one-letter verdict in read state produce the back configuration at position $p$ with bookmark $0$ and depart state carrying the verdict and the side value specified in the statement; the input-head position and output are preserved.

**Proof.** The one-letter buffer tape is the tape that is blank everywhere except for the verdict at cell $0$. This follows from the buffer-append identity applied to the empty word (`Turing.FinTM.bufferTape_append`). Expand the two transitions and compare configuration fields. The dispatch rules move the machine from read through restore to depart, place the verdict and the prescribed optional side in the state, and leave the bookmark at zero. The tape updates agree pointwise: the buffer's sole letter is at cell $0$, while the other updated cells match the back configuration. Both transitions preserve the input-head position and output, so the configurations agree.

**Key facts.** `Turing.FinTM.bufferTape_append`.
