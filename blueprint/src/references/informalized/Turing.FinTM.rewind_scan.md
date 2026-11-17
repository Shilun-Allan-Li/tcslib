<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.rewind_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leftward Scan to the Input Start

**Claim.** Under the stated transition rule, a configuration in the scan state at input-head position $p\le |x|$ reaches the destination state at position $1$ after exactly $p+1$ steps, with every other configuration component unchanged.

**Proof.** Prove the claim first for a specified position $j$, by induction on $j$. If $j=0$, the head is at position $0$, where the scanned symbol is blank. The transition therefore moves right and enters the destination state; the input head ends at position $1$, and the transition leaves the other components unchanged. For the successor case, $j+1$, the head is over the input symbol $x[j]$ (`inputSymbolInner`). The transition stays in the scan state and moves left, producing a configuration at position $j$ (`moveInputPos_neg_val`), without changing the other components. The run decomposition for one initial step (`runFrom_succ_eq_step`) reduces the remaining run to the induction hypothesis at position $j$. Thus after $(j+1)+1$ steps the claimed configuration is reached. Finally, instantiate this position-indexed statement with the configuration's actual input-head position.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.inputSymbolInner`, `Turing.FinTM.moveInputPos_pos_of_ne_right`.
