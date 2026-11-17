<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_replay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replay of a Nonhalting Run

**Claim.** If the stopped table interpreter is live after $t$ steps, then after $t$ steps the timed interpreter from the corresponding lift has reached the lift of that stopped configuration, with the clock word unchanged.

**Proof.** Induct on $t$. At zero steps, both runs are their initial configurations, so the claim is immediate. For the successor step, the run-length identity (`runFrom_succ_eq_step'`) expresses each run at time $t+1$ as one step after time $t$. The assumed liveness at time $t+1$ implies liveness at time $t$ (`timedCut_live_before`), so the induction hypothesis identifies the timed and stopped configurations at that earlier time. The same liveness condition, together with $t<t+1$, ensures that the stopped configuration at time $t$ is not in an `applyRecord` state (`timedCut_no_record`). The one-step replay result (`timed_regular_step`) therefore applies; combining it with the run-length identity proves the successor case.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timedCut_live_before`, `Turing.timedCut_no_record`, `Turing.timed_regular_step`.
