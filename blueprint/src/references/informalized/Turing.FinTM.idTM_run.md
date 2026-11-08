<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.idTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy Machine Run Invariant

**Claim.** For every Boolean word $x$ and every $t\le |x|$, after $t$ steps the copy machine is in its unique state, its input head is at position $t+1$, and its output is the length-$t$ prefix of $x$.

**Proof.** Proceed by induction on $t$. At $t=0$, the initial configuration has the unique state, head position $1$, and empty output, as required. For the successor step, use the induction hypothesis to know that the machine is still in its unique state and its head is at position $t+1$. Since $t<|x|$, the input symbol read there is $x[t]$ (`inputSymbolInner`). The copy machine emits that symbol, keeps its state, and moves the input head one place to the right. The new position is therefore $t+2$ (`moveInputPos_pos_of_ne_right`), and appending the emitted symbol to the old output gives the prefix of length $t+1$. The transition from the $t$-step run to the next run is justified by the successor law for iteration (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`.
