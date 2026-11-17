<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_prepared_eval_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Return of the Prepared Evaluation

**Claim.** When $M$ computes $o$ from $s$ in exactly $T$ steps, the prepared evaluator first reaches its return state at some positive time $t\le 1+2T+|s|+2$, and at that time it is the evaluator configuration of the halted tracked run after the right-boundary scan.

**Proof.** The computation hypothesis gives that the source run halts at time $T$ and has output $o$ (`Turing.FinTM.computesInTime_iff`). Tracking this run takes $1+2T$ steps (`Turing.FinTM.emCall_track_computes`), and the right-boundary wrapper then computes the same output in a further $|s|+2$ steps (`Turing.FinTM.emCall_right_computes`). Apply the evaluator's first-return result to this wrapped computation, with deadline $D=1+2T+|s|+2$. It gives a return time $t\le D$, no earlier return, and the evaluator configuration at $t$ as the wrapped configuration at that time (`Turing.FinTM.emCall_eval_first`). The time is positive: if $t=0$, the first-return assertion would say the initial evaluator configuration is already in its return state, contrary to its initial state. Since the wrapped computation has halted by time $D$, its run remains unchanged after its halting time; the run composition law and halting stability (`Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`) therefore identify its configuration at $t$ with its configuration at $D$. The tracked-run identity at time $1+2T$ (`Turing.FinTM.emCall_track_run`) and the right-endpoint result identify that final configuration with the scan configuration built from the halted tracked run, as required.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.emCall_track_computes`, `Turing.FinTM.emCall_right_computes`, `Turing.FinTM.emCall_eval_first`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.FinTM.emCall_track_run`, `Turing.FinTM.emCall_right_endpoint`.
