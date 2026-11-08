<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_interpret_finishes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Interpreter Completion

**Claim.** Given the stated bounds on the table position and clock value, the timed interpreter reaches a halted configuration whose output is the deadline-inclusive answer after $r$ simulated steps, within the stated step bound.

**Proof.** Proceed by induction on the deadline $r$, proving the assertion uniformly for every source configuration, table position, and clock word satisfying the hypotheses.

1. If the source is already halted, the timed interpreter flushes the buffered output and halts after $2|\mathrm{src.output}|+3$ steps. The flush result gives the desired answer, and this duration is within the bound. This handles both deadline zero and a positive deadline, since a halted source remains unchanged under further simulated steps.

2. Suppose the source is live. The live-block cut lemma (`Turing.timedCut_live_block`) says that within $3|M.\mathrm{serialize}|+5(M.\mathrm{numStates}+1)+20$ steps the universal interpreter reaches an action record for the next simulated transition, with a valid table position. Replay preserves this computation in the timed interpreter (`Turing.timed_replay`).

3. At deadline zero, the clock has value zero. The timeout rule (`Turing.timed_clock_timeout`) therefore halts after a further $2|bs|+3$ steps and returns the negative answer, as required when a live source has not halted by time zero. Combining the cut and timeout durations yields the claimed bound.

4. For a positive deadline, the clock value is positive. The clock-success rule (`Turing.timed_clock_success`) executes the recorded transition and replaces the clock by its borrowed, decremented form. The borrow-value identity (`Turing.timedBorrow_value`) shows that this new clock represents deadline $r$, while the borrow-length identity (`Turing.timedBorrow_length`) preserves its length. Apply the induction hypothesis to the machine’s one-step successor configuration, the updated table position, and this decremented clock.

5. The machine’s output grows by at most one symbol in a single step, by the output-update formula (`Turing.MultiTapeTM.step_output`). Thus the induction bound for the successor, together with the cut and clock-success durations, is bounded by the claimed expression for deadline $r+1$. The run-addition and successor-run identities (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`) concatenate these stages and identify the resulting output with the deadline-inclusive answer.

**Key facts.** `Turing.timed_flush`, `Turing.timedCut_live_block`, `Turing.timed_replay`, `Turing.timed_clock_timeout`, `Turing.timed_clock_success`, `Turing.timedBorrow_value`, `Turing.timedBorrow_length`, `Turing.MultiTapeTM.step_output`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
