<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapStart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of the Threaded-Map Controller

**Claim.** If $M$ computes $w$ on $x$ within the stated time and space bounds, then there is a time $t\leq T+|w|+|x|+5$ and a configuration $c$ of $M$ with output $w$ such that the threaded-map controller reaches the silent validation state with input head at $1$, capture displacement $0$, and empty output, while retaining $c$'s simulated tapes and head positions.

**Proof.** Choose the least time $t_0$ at which the run of $M$ on $x$ halts, and let $c$ be its configuration then. The time bound gives $t_0\leq T$, and `computesInTime_iff` identifies halting and output at a specified time with computation in time; in particular $c$ has output $w$. Output uniqueness (`ComputesInTime.output_unique`) also records that this least halting run has the prescribed output. The capture simulation lemma `capture_run` shows that the threaded controller simulates this live prefix of $M$ while storing its output on the added tape. At the next step, the transition out of the captured halting configuration enters the controller's rewind phase, with the added tape positioned at the end of the captured output. The controller then rewinds over that buffer and returns to the input start; `mapBuffer_rewind` accounts for this rewind, and `catalogRewind` supplies the bounded scan back to input position $1$. Combining the phases with `runFrom_succ_eq_step'` and `runFrom_add` gives the displayed target configuration. The total time is $t_0+1+(|w|+1)+r$, where `catalogRewind` bounds $r$ by the input-head position plus $2$; since that position is at most $|x|+1$, and $t_0\leq T$, this is at most $T+|w|+|x|+5$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.capture_run`, `Turing.FinTM.catalogRewind`, `Turing.FinTM.mapBuffer_rewind`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`.
