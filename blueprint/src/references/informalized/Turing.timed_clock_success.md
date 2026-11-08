<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_success -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Executing a transition with positive budget

**Claim.** If the pending-action configuration has positive clock value, then after $2|b_s|+4$ steps the timed interpreter reaches the lift of one universal-interpreter step, with clock word obtained by subtracting the incoming borrow from $b_s$.

**Proof.** First show the final carry from subtracting one is false. If it were true, the borrow-underflow criterion (`timedBorrow_underflow`) would imply that the clock value is zero, contradicting its positivity. Apply the complete clock pass (`timed_clock_pass`) to reach borrow control at the end of the word; the carry is therefore false. The result word has the same length as the original (`timedBorrow_length`), so the head at index $|b_s|$ reads no symbol, as follows from the natural-index description of the buffer tape (`bufferTape_nat`) and the list lookup beyond its length. At this configuration, the interpreter's transition with false carry enters execute control and otherwise preserves the lifted data. The input head remains fixed by `moveInputPos_zero`, and the tape and head components agree by the definitions of the lift and transition. Two final interpreter steps carry out the universal transition, by `timed_execute`. Splitting the run into the clock pass and these two steps via the successor run equation (`runFrom_succ_eq_step'`) gives the claimed total of $2|b_s|+4$ steps.

**Key facts.** `Turing.timedBorrow_underflow`, `Turing.timed_clock_pass`, `Turing.timedBorrow_length`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`, `Turing.timed_execute`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
