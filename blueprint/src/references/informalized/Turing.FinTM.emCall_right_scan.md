<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_right_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Rightward Scan

**Claim.** After $r+1$ steps, the right-boundary wrapper from the scan configuration at position $j+1$ is halted at position $|x|+1$, with the other components of the specified halted scan configuration.

**Proof.** Induct on $r$. If $r=0$, the equation $j+r=|x|$ gives $j=|x|$. The head is already at the right boundary, so its input symbol is blank; the wrapper halts and leaves the head position and all other configuration data unchanged. For the successor case, $r+1$ remaining positions implies $j<|x|$, so the head reads the symbol $x[j]$. In the scanning state the wrapper moves right, leaves the work tapes and output unchanged, and remains in that state. Thus its first step produces the scan configuration at position $(j+1)+1$. The induction hypothesis applies to the remaining $r+1$ steps, since $(j+1)+r=|x|$, and yields the claimed halted configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.inputSymbolInner`, `Turing.controlAction_apply`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_zero`.
