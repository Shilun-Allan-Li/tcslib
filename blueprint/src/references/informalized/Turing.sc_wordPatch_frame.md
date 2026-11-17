<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_wordPatch_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame agreement for equal-length patches

**Claim.** If a tape agrees with a word $u$ at all offsets from $-1$ through its length, then patching the tape with an equal-length word $v$ makes the patched tape agree with $v$ at all offsets from $-1$ through its length.

**Proof.** Fix an allowed offset $p$. If $c_p+p$ lies inside the interval overwritten by the patch, the patch supplies the buffer-tape content of $v$ at offset $p$, since subtracting the base position recovers $p$. Otherwise, the bounds on $p$ and the equal lengths force $p$ to be either $-1$ or the right endpoint $|v|$. At the left endpoint, the original tape agrees with the buffer tape of $u$, which is blank there; both buffer tapes are blank at offset $-1$ (`FinTM.bufferTape_left`). At the right endpoint, the original tape agrees with $u$ there, and equal lengths make the buffer-tape contents of $u$ and $v$ at that endpoint equal. Thus the patched tape agrees with $v$ at every required offset.

**Key facts.** `Turing.FinTM.bufferTape_left`.
