<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCopy_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Copy-Loop Tape

**Claim.** For every Boolean word $w$, the tape $T([],w)$ is $\mathrm{buffer}(w)$.

**Proof.** At a cell $z<0$, the buffer is blank, and the defining cutoff for $T([],w)$ also makes the cell blank. At a cell $z\ge0$, the cutoff does not blank the cell, and $T([],w)$ reads precisely from $w$ at that position, as does the buffer. The tapes therefore agree at every cell.
