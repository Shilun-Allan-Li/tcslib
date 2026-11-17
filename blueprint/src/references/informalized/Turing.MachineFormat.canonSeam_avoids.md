<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonSeam_avoids -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Avoiding a target across a machine seam

**Claim.** Under the stated hypotheses on the runs of $A$ and $B$, their seam composition avoids the target state at every time less than $t+1+v$.

**Proof.** Fix a time $u<t+1+v$ and split according to whether $u\le t$. In the first case, the seam-composition run still agrees with the run of $A$, with its states relabeled to the left summand (`seamCompTM_runFrom_left`). The assumed avoidance through time $t$ therefore excludes the target at $u$. In the other case, write $u=t+1+r$. At time $t+1$, seam composition has reached the exit of $A$ and takes its transition into the entry of $B$; thereafter the run agrees with $B$ from the relabeled exit configuration (`seamCompTM_run_ofCfg`). Since $u<t+1+v$, we have $r<v$, so the assumed avoidance during the first $v$ steps of $B$ excludes the target at this time as well.

**Key facts.** `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM_run_ofCfg`.
