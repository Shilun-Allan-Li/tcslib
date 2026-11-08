<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rewind_scan_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Heads During a Leftward Scan

**Claim.** During the first $j+1$ steps of the specified leftward scan from position $j\le |x|$, the work-tape head positions remain equal to their initial positions.

**Proof.** Induct on the input-head position $j$. If $j=0$, the allowed times are $0$ and $1$. At time $0$ the claim is immediate; at time $1$, the blank transition moves only the input head, so the work-head positions are unchanged. For the successor case, time $0$ is again immediate. At any positive allowed time, the current head is over $x[j]$ (`inputSymbolInner`), so the transition stays in the scan state and moves the input head left, without moving any work head. Decomposing the run into this first step and the remaining steps (`runFrom_succ_eq_step`), the latter are covered by the induction hypothesis at position $j$: the input position has decreased from $j+1$ to $j$ (`moveInputPos_neg_val`), and the time bound decreases accordingly. Hence the work-head positions remain unchanged for the full stated interval.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.inputSymbolInner`.
