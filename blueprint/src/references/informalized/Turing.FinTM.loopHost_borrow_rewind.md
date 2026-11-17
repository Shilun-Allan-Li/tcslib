<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_borrow_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Counter Head

**Claim.** For every $j\le |w|$, the specified run from phase $9$ or $10$ takes $j+1$ steps, preserves the counter word and the other framed data, and ends with the counter head at zero in the stated released call or phase $11$.

**Proof.** Apply the scan-left principle to the family of configurations whose counter head is at $j-1$. For each positive scan position, the counter cell is the corresponding bit of $w$: the counter-track projection identifies the scanned tape, and the natural-position buffer rule reads that bit. In either starting phase, the host moves left when a bit is present, leaving the counter unchanged; the control action therefore gives the preceding scan configuration. At the initial position $j=0$, the head is at $-1$, where the buffer is blank. The host then moves right without writing, exiting to the released next-anchor call when success is true and to phase $11$ otherwise. These one-step descriptions supply the scan hypotheses, so the scan-left principle gives the claimed run for every $j\le |w|$.

**Key facts.** `Turing.FinTM.loop_scan_left`, `Turing.FinTM.loopFrame_counter`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.loopControl_apply`.
