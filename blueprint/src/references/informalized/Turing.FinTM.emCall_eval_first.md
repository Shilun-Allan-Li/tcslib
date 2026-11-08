<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_eval_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halting Time of the Evaluator

**Claim.** If $M$ halts on $s$ with output $o$ by time $T$, there is a first halting time $t\le T$ and a boundary tag satisfying the stated conditions: the evaluator has not returned earlier, and at time $t$ its configuration matches the evaluator configuration associated with $M$ at that time.

**Proof.** The computation characterization (\texttt{computesInTime\_iff}) gives a halting configuration at time $T$. Choose $t$ to be the least time at which the run of $M$ is halted. Then $t\le T$, the run is live at every earlier time, and the configuration at $t$ has output $o$: the output uniqueness theorem (\texttt{ComputesInTime.output\_unique}) identifies its output with the one certified at time $T$. Initially the input head is at position $1$, so the true tag satisfies the boundary condition. The evaluator simulation theorem (\texttt{emCall\_eval\_run}), applied to the live run through time $t$, supplies a valid tag at time $t$ and identifies the evaluator's configuration there. For any $j<t$, apply the same simulation through time $j$. The simulated machine is still live at $j$, so the evaluator state is an active simulation state, not its return state. This proves both the asserted non-return property and the configuration equality at $t$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.emCall_eval_run`.
