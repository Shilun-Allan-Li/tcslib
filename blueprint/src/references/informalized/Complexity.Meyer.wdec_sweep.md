<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineWalk.lean :: Complexity.Meyer.wdec_sweep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sweep Across a Boolean Word

**Claim.** Starting with $i$ true bits, then $j$ false bits, then the remaining word, the waiting-decision state sweeps across the $j$ false bits, changing them to true. After $j$ steps the first $i+j$ bits are true, the remainder is unchanged, and the auxiliary head is at $i+j$.

**Proof.** Induct on the number $j$ of false bits to be swept, with the initial true-prefix length $i$ arbitrary. When $j=0$, no transition is taken, and the claimed configuration is the starting one. For the induction step, the auxiliary head is at position $i$, where the tape contains the first of the $j+1$ false bits. Indeed, the indexed-read fact for `bufferTape` ( `Complexity.Meyer.bufferTape_at`) and the list layout show that this scanned cell is false. The one-step waiting-decision rule ( `Complexity.Meyer.wdec_zero`) therefore changes that cell to true, moves the head to $i+1$, and leaves the machine in the waiting-decision state. Updating the buffer tape at the middle of its concatenated lists gives precisely the layout with $i+1$ true bits followed by $j$ false bits and the same remainder ( `Complexity.TimeHierarchy.bufferTape_update_mid`). Now apply the induction hypothesis with prefix length $i+1$ to sweep those remaining $j$ bits. The decomposition of a run of $j+1$ steps into one step followed by $j$ steps justifies this composition ( `Turing.MultiTapeTM.runFrom_succ_eq_step`). Associativity and commutativity of natural-number addition identify the final prefix length and head position as $i+j+1$.

**Key facts.** `Complexity.Meyer.bufferTape_at`, `Complexity.Meyer.wdec_zero`, `Complexity.TimeHierarchy.bufferTape_update_mid`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
