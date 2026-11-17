<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBorrow_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding After a Borrow

**Claim.** For each $j$ with $0\le j\le |u|$, the debit machine starting in the borrow-result state with head at $j-1$ and tape $u$ reaches the terminal result state after $j+1$ steps, with head at zero and tape unchanged.

**Proof.** Induct on $j$. For $j=0$, the head is at $-1$, so the scanned tape cell is blank (`bufferTape_left`). The machine's transition moves the head right to zero and enters the terminal state carrying the same Boolean; the zero input-head movement leaves the input position fixed (`moveInputPos_zero`). The run-at-zero and successor-run identities (`runFrom_zero`, `runFrom_succ_eq_step`) identify this as the required one-step run. For the successor case, the starting head position is $(j+1)-1=j$. Since $j<|u|$, cell $j$ contains the corresponding entry of $u$ (`bufferTape_nat`). In the borrow-result state, either value is left unchanged while the head moves one position left and the state remains the same. Thus the first step reaches the induction hypothesis's starting configuration, with head at $j-1$; applying the induction hypothesis for the remaining $j+1$ steps gives the terminal configuration after the total of $j+2$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.bufferTape_left`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`.
