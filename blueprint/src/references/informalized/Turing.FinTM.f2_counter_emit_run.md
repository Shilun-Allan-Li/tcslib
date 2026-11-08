<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_emit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Output at Each Step

**Claim.** For every Boolean list $x$, valid input-head position $p$, and Boolean list $bs$, at each time $i\le |bs|$ the counter machine remains in state $3$, with its input-head and work-tape-head positions and tape unchanged, and output equal to the first $i$ entries of $bs$.

**Proof.** Induct on $i$. At time zero the run is the specified starting configuration, and the output is the empty prefix. For the successor step, apply the induction hypothesis at time $i$ and read the symbol at position $i$ of the tape. Since $i<|bs|$, that symbol is $bs[i]$. The state-$3$ transition emits precisely this symbol, preserves the tape and both head positions, and stays in state $3$. The input head is unchanged because its movement is zero (`moveInputPos_zero`). Appending the emitted bit to the previously produced prefix gives the prefix of length $i+1$ (`runFrom_succ_eq_step'` expresses this one-step extension of the run).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
