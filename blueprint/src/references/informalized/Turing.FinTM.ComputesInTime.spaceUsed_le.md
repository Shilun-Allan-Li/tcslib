<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.ComputesInTime.spaceUsed_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound from Running Time

**Claim.** If $M$ computes $y$ from $x$ within $T$ steps, then for every $t$, the total number of work-tape cells visited through step $t$ is at most $k(T+1)$, where $k$ is the number of work tapes.

**Proof.** The computation-time hypothesis implies that the run from the initial configuration is halted at time $T$ (`computesInTime_iff`). Fix a tape. A head position visited by time $t$ is the position at some time $u\le t$. If $u\le T$, that position occurs among the positions visited through time $T$. If $u>T$, write $u=T+(u-T)$. The run is already halted at time $T$, so it remains in the same configuration thereafter (`runFrom_add` and `runFrom_of_halt`); thus the position at time $u$ is the one at time $T$, also visited through time $T$. Hence each tape's set of positions visited through $t$ is contained in its set through $T$. The latter is the image of the $T+1$ time indices $0,\ldots,T$, so it has at most $T+1$ elements. Summing this bound over the $k$ work tapes gives $k(T+1)$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
