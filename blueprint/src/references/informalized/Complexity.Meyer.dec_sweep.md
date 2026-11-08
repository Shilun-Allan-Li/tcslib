<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.dec_sweep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Sweep Across a Boolean Buffer

**Claim.** For all natural numbers $i,j$ and every Boolean word $rest$, starting the simulator in its decode state with $i$ true bits followed by $j$ false bits and then $rest$, and with its $C$ head at $i$, after $j$ steps the buffer has $i+j$ true bits followed by $rest$ and the head is at $i+j$; the other listed configuration data are unchanged.

**Proof.** Induct on $j$, keeping $i$ arbitrary. When $j=0$, the starting buffer and head already have the claimed form. For the successor case, the buffer has a false symbol at position $i$, since the first $i$ entries are true and the next block begins with false (`bufferTape_at`). One decode step therefore changes that cell to true and advances the head to $i+1$ (`dec_zero`). Updating the buffer at the boundary between the initial block and its remainder converts $i$ true bits followed by $j+1$ false bits and $rest$ into $i+1$ true bits followed by $j$ false bits and $rest$ (`bufferTape_update_mid`). The induction hypothesis, applied with starting index $i+1$, handles the remaining $j$ steps. The iterate law for machine runs identifies the successor run with one step followed by those $j$ steps (`runFrom_succ_eq_step`), and the resulting arithmetic rearranges the final block length to $i+j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.Meyer.bufferTape_at`, `Complexity.Meyer.dec_zero`, `Complexity.TimeHierarchy.bufferTape_update_mid`.
