<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.print_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftward Walk During Register Printing

**Claim.** During the leftward walk that prints a register whose tape contains $m$ consecutive ones from cell $0$, starting with its head at cell $j-1$ leads after $j+1$ steps to the print-right state with its head at cell $0$ and with $j$ ones appended to the output, for every $j\le m$. The input position and tapes remain unchanged.

**Proof.** Induct on $j$. When $j=0$, the head begins at cell $-1$, which is blank because the tape has ones only at cells $0,\ldots,m-1$. The transition rule for the leftward printing state therefore changes to the print-right state, leaves the head at cell $0$, and prints nothing; the input position and tape contents are unchanged. This is the required result after one step. For the successor case, suppose $j+1\le m$. The head starts at cell $j$, which contains a one, since $0\le j<m$. The leftward printing rule prints that one and moves the head one cell left, to cell $j-1$, while remaining in the leftward state. The tape itself is not modified. The induction hypothesis now applies with index $j$ and the output already extended by one bit: after a further $j+1$ steps it reaches the print-right state with its head at zero and appends $j$ more ones. Together, the first transition and these steps take $(j+1)+1$ steps and append $j+1$ ones. The zero input movement leaves the input-head position unchanged (\texttt{moveInputPos\_zero}); the one-step machine transition and action formulas (\texttt{step\_some}, \texttt{apply\_act}) give the stated effects on state, tape, head, and output. The tape-content checks use that nonnegative cells below $m$ contain ones (\texttt{ones\_lt}) and negative cells are blank (\texttt{ones\_neg}).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.CounterProg.step_some`, `Complexity.CounterProg.apply_act`, `Turing.UnaryTape.ones_neg`, `Turing.UnaryTape.ones_lt`, `Turing.moveInputPos_zero`.
