<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.timed_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound to Reach the Selected Branch

**Claim.** If the decider computes output $[b]$ on $x$ in $T$ steps, then within $2T+5$ controller steps it reaches a branch-phase configuration built from the branch machine selecting $b$, for suitable contents and head positions of the decider-tape block.

**Proof.** Choose the earliest time $t$ at which the decider is halted. Since it is halted at time $T$, this earliest time satisfies $t\le T$. The computation-time characterization gives that the output at time $t$ is also $[b]$: both this halted run and the stated computation have the same unique output (`computesInTime_iff`, `ComputesInTime.output_unique`). Until time $t$, the decider is live, so the controller tracks it in its capture phase (`timed_control_init`, `timed_capture`). From the resulting halted decider-phase configuration, two controller steps read the stored bit and reach the ready configuration (`timed_read`). The rewind routine then moves to the input start and enters the selected branch state (`timed_rewind`). The input-head bound ensures that this rewind takes at most the current input-head position plus two steps (`timed_input_bound`). Thus the total time is $t+2+r$, with $r\le 1+t+2$, so it is at most $2t+5\le 2T+5$. The decider's tape contents and head positions supply the required choices for the decider-tape block; splitting the run into these successive intervals uses `runFrom_add`.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.ComputesInTime.output_unique`, `Turing.FinTM.timed_control_init`, `Turing.FinTM.timed_capture`, `Turing.FinTM.timed_read`, `Turing.FinTM.timed_rewind`, `Turing.MultiTapeTM.timed_input_bound`, `Turing.MultiTapeTM.runFrom_add`.
