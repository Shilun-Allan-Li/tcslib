<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_right_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation Before the Source Halts

**Claim.** If the source run from configuration $c$ is live at every time $j<t$, then after $t$ steps the right-boundary wrapper started from the embedding of $c$ equals the embedding of the source configuration after $t$ steps.

**Proof.** Proceed by induction on $t$. At time zero, both runs are at their specified starting configurations. For the successor step, the induction hypothesis identifies the two runs at time $t$. The source is live at that time by the hypothesis, so one transition of the right-boundary wrapper agrees with the embedding of one source transition (`Turing.FinTM.emCall_right_step`). The successor-time characterization of an iterated run then identifies the resulting configurations at time $t+1$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`).

**Key facts.** `Turing.FinTM.emCall_right_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
