<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopCopy_final -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Copy-Loop Tape

**Claim.** For every Boolean word $w$, the tape $T(w,[])$ is the blank tape $\mathrm{buffer}([])$.

**Proof.** Check the tapes at an arbitrary cell $z$. If $z<|w|$, the definition of $T(w,[])$ makes the cell blank, as does the empty buffer. Otherwise $z\ge |w|\ge0$. The buffer lookup in $T(w,[])$ is then an index at or beyond the end of $w$, so it is blank; the empty buffer is blank there as well. Thus the tapes agree at every cell.
