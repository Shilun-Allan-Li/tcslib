<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_back -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the clock head

**Claim.** For each $j\le |b_s|$, starting in the clock-rewind phase with clock word $b_s$ and head at $j-1$, after $j+1$ steps the interpreter is in the borrow phase with borrow flag true, the same clock word, and head at $0$.

**Proof.** Proceed by induction on $j$. When $j=0$, the head is at $-1$; one transition moves it right to $0$ and changes control to the borrow phase with flag true. This is the zero-position instance of the single-step clock transition fact (`timedClock_step`), together with the zero-step run identity. For the successor case, the clock head is at position $j$, where the tape contains the $j$th bit of $b_s$ by the natural-index description of the buffer tape (`bufferTape_nat`). The clock-rewind transition moves the head one place left while preserving the rewind control and clock word. After this step, the induction hypothesis applies to the remaining $j+1$ steps, yielding the borrow phase at head position $0$. The run equations split off the first step and simplify the head arithmetic.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.timedClock_step`, `Turing.FinTM.bufferTape_nat`.
