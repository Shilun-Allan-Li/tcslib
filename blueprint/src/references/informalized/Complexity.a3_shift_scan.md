<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_shift_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanning invariant for the shift machine

**Claim.** For each $t\le |x|$, after $t$ steps the machine is in its scanning state, its input head is at position $t+1$, and its output is exactly $t$ false bits.

**Proof.** Induct on $t$. At $t=0$, the initial configuration has the scanning state, the input head at position $1$, and empty output. For the successor case, the induction hypothesis and $t+1\le |x|$ imply that the input head is reading the $t$th symbol of $x$. The input-symbol identity identifies that symbol (Turing.inputSymbolInner). The scanning transition moves the input head one position to the right, emits one false bit, and remains in the scanning state. The position therefore becomes $t+2$, and appending one false bit to the existing output gives the list of $t+1$ false bits. The relation between a run of $t+1$ steps and the preceding configuration followed by one step is the run-successor identity (Turing.MultiTapeTM.runFrom_succ_eq_step'); the rightward head movement has the asserted position (Turing.moveInputPos_pos_of_ne_right).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
