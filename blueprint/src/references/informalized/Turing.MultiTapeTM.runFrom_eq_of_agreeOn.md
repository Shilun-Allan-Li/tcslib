<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.MultiTapeTM.runFrom_eq_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Along Visited States

**Claim.** If two machines have matching transitions on a set of states and the first run remains in that set before time $t$, then their configurations after $t$ steps are equal.

**Proof.** Proceed by induction on $t$. At time zero the runs start at the same configuration. For the successor case, write each run at time $t+1$ as one step from its configuration at time $t$ (`runFrom_succ_eq_step'`). The induction hypothesis, applied to the guard restricted to times before $t$, identifies the two configurations at time $t$. The first machine’s state there belongs to the specified set by the guard, so the machines’ transitions agree at that configuration (`step_eq_of_agreeOn`). Their next configurations are therefore equal.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.step_eq_of_agreeOn`.
