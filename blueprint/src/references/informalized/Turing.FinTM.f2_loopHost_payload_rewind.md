<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_payload_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload Tape Rewind

**Claim.** For each $j\leq |w|$, the host in phase $12$ with payload $w$ and its head at $j-1$ reaches phase $13$ after $j+1$ steps, preserving the tape and all other specified data, with the payload head at zero.

**Proof.** Induct on $j$. For $j=0$, the head is at $-1$, so the buffer tape is blank there (`bufferTape_left`). The phase-$12$ transition moves right to zero and enters phase $13$, without changing the tape or other specified data. For the successor case, the head starts at the natural position $j$. Because $j<|w|$, that position contains the $j$th symbol of $w$, by the buffer-tape and list-index identities. The phase-$12$ transition consequently moves left and stays in phase $12$, producing the configuration for the induction hypothesis at index $j$. Apply the hypothesis for the remaining $j+1$ steps. The run decomposition yields $(j+1)+1$ steps in total and final head position zero.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.f2_loopFrame_payload`, `Turing.FinTM.f2_loopControl_apply`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
