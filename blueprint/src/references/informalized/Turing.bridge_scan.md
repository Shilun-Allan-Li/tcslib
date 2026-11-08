<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Input Scan

**Claim.** For every $j\leq |x|$, after exactly $j$ steps on the embedded Boolean input, the bridging machine is scanning at input-head position $j+1$, with every stack and the output empty.

**Proof.** Induct on $j$. At $j=0$, the initial configuration has the scanning state, head position $1$, empty stacks, and empty output; the empty-stack representation facts (`bridgeStack_nil`, `bridgeStore_nil`) identify it with the claimed bridge configuration. For the successor case, the run recurrence (`runFrom_succ_eq_step'`) reduces the claim to one transition from the inductive configuration. Since $j<|x|$, the input symbol at position $j+1$ is the embedded bit $x_j$ (`inputSymbolInner`). In the scanning state, any present input symbol causes the machine to move the input head one position to the right and remain scanning, without changing the stacks or output (`bridge_step`). The right-move fact (`moveInputPos_pos_of_ne_right`) gives position $j+2$, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.bridgeStack_nil`, `Turing.bridgeStore_nil`, `Turing.bridge_step`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
