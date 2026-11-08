<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_fuel_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Synchronized Counter Rewind

**Claim.** From controller phase $3$ with counter tape storing $w$, blank payload tape, both heads at $j-1$, and output $o$, where $j\le |w|$, the host reaches phase $4$ after $j+1$ steps. The counter and output are unchanged, the payload remains blank, and both heads are at $0$.

**Proof.** Apply the left-scan principle `loop_scan_left` to the sequence of phase-$3$ configurations indexed by the counter position. At a positive index $j$, the head is at $j$ when the next transition is taken. Since $j\le |w|$, this is a cell of the word and hence nonblank (`bufferTape_nat`); the phase-$3$ transition moves both heads left and remains in phase $3$. The frame update is described by `loopControl_apply`, leaving the counter contents, payload, and output unchanged. At index zero, the head is at $-1$, where every buffer tape is blank (`bufferTape_left`); the transition moves both heads right to $0$ and enters phase $4`. The scan principle now gives the asserted run of $j+1$ steps, including $j=0$.

**Key facts.** `Turing.FinTM.loop_scan_left`, `Turing.FinTM.loopFrame_counter`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.bufferTape_left`, `Turing.FinTM.loopControl_apply`.
