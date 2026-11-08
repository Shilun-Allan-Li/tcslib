<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_right_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completing the Rightward Scan

**Claim.** Starting from the embedding of a halted configuration $c$ on input $x$, the right-boundary wrapper reaches the halted scan configuration with input head at position $|x|+1$ within $|x|+2$ steps.

**Proof.** The wrapper first takes one control step to enter its rightward-scan state. Its head moves one cell right, and the control-action formula shows that the tapes, work-head positions, and output are unchanged (`Turing.FinTM.controlAction_apply`). If the new head position is $j+1$, then $j\le |x|$. The wrapper's scan rule advances right while it reads input symbols; after $r=|x|-j$ further cells it reaches the right boundary, and one final step halts there. The scan lemma gives exactly this transition sequence from the configuration at the start of the scan to the halted endpoint (`Turing.FinTM.emCall_right_scan`). Thus the total number of steps is $1+(r+1)\le |x|+2$.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.emCall_right_scan`.
