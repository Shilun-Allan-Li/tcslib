<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_succ_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Successor Run

**Claim.** Starting in the successor machine’s increment phase with tape $i$ holding the buffered word $w$ on the specified offsets, the machine first reaches its exit phase within $4|w|+14$ steps. It writes the successor word on that tape, preserves the other configuration data, and keeps every work-tape head within distance $|w|+4$ of its initial position throughout.

**Proof.** First view the starting configuration as one for the increment machine in its run state. The extra endpoint hypothesis supplies the buffer information needed for the increment phase. Split on whether the fixed-width increment of $w$ succeeds.

If it succeeds with result $v$, the increment-run theorem (`Turing.incrementTM_run_succ_ofCfg`) gives a completed true-flag configuration, its first-completion property, and head bounds. The handoff theorem (`Turing.rt_succ_increment`) transfers this run to the successor machine and redirects the completed state to the exit phase. The fixed-width result has the same length as $w$ (`Turing.rt_incFixed_length`), so the tape contents are exactly the successor word. The chosen time is the increment completion time plus the redirect step; it is bounded by $4|w|+14$, and the increment head bounds imply the stated radius.

If the fixed-width increment overflows, `Turing.incrementTM_run_overflow_ofCfg` says that the increment phase returns with a false flag and the word replaced by zeros. The handoff theorem dispatches this configuration into the extension phase. The append-symbol run theorem (`Turing.rt_appendSymbol_run`) then writes a one immediately after those zeros, returns to the appropriate position, and gives the first arrival at its exit. The phase-host run theorem (`Turing.phaseHostTM_run`) joins that extension run to the successor machine and transfers its exit state. The run-addition identity (`Turing.MultiTapeTM.runFrom_add`) combines the increment and extension durations. The appended-buffer identity (`Turing.FinTM.bufferTape_append`) identifies the resulting zeros followed by one with the successor word in the overflow case. The two stage bounds give the total $4|w|+14$; their head-radius estimates yield $|w|+4$.

**Key facts.** `Turing.incrementTM_run_succ_ofCfg`, `Turing.rt_succ_increment`, `Turing.rt_incFixed_length`, `Turing.incrementTM_run_overflow_ofCfg`, `Turing.rt_appendSymbol_run`, `Turing.phaseHostTM_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.bufferTape_append`.
