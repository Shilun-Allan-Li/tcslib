<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator Emission and Turnaround

**Claim.** For every bit string $x$ and output string $w$, running the machine for three steps from state $0$, with input head at the right boundary position $|x|+1$ and output $w$, yields state $4$, with input head at position $|x|$ and output $w$ followed by $01$.

**Proof.** Break the three-step run into three successive transitions. At each transition the head is still at the right boundary, so it scans no symbol (`Turing.pairDiag_right`). The transition from state $0$ emits the first separator bit $0$ and keeps the head fixed; the transition from state $2$ emits $1$ and again keeps it fixed. The transition from state $3$ emits nothing, enters state $4$, and moves the head one position left, from $|x|+1$ to $|x|$. Composing these transitions gives output $w$ followed by $01$. The run equations identify the three-step computation with those successive steps (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`); the zero and leftward head movements have the stated positions (`Turing.moveInputPos_zero`, `Turing.moveInputPos_neg_of_ne_left`). Equality of the resulting zero-work-tape configurations follows from agreement of state, input position, and output (`Turing.Cfg.ext_zero_tapes`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.pairDiag_right`, `Turing.moveInputPos_zero`, `Turing.moveInputPos_neg_of_ne_left`, `Turing.Cfg.ext_zero_tapes`.
