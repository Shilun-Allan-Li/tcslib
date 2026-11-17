<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_fuel_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Tape Rewind

**Claim.** For each $j\leq |w|$, the host in phase $1$ with payload tape $w$ and head at $j-1$ reaches phase $2$ in $j+1$ steps, with the tape unchanged and its head at zero.

**Proof.** Proceed by induction on $j$. At $j=0$, the head is at $-1$, where the buffer tape is blank (the fact `bufferTape_left`). Thus phase $1$ detects the blank cell, moves the head right to zero, and enters phase $2`; the phase action updates only the control state and payload-head position. For the successor case, the payload head starts at the natural position $j$. Since $j<|w|$, it reads the $j$th symbol of $w$ (using `bufferTape_nat` and the list-index identity). Phase $1$ therefore moves left one cell and remains in phase $1$, leaving the tape and all other specified data unchanged. This single step produces precisely the induction-hypothesis configuration with index $j$. Apply that hypothesis for the remaining $j+1$ steps; the run-length decomposition gives the claimed total of $(j+1)+1$ steps and final head position zero.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.f2_loopFrame_payload`, `Turing.FinTM.f2_loopControl_apply`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
