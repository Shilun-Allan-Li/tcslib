<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Lockstep.runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation by Total Cost

**Claim.** If the original machine avoids $X$ at each of the first $t$ times, then the simulated machine run for the sum of those configurations' costs reaches the encoding of the original configuration at time $t$.

**Proof.** Induct on $t$. At zero steps, both the accumulated cost and the original run length are zero, so the result is the initial encoding. For the successor step, split off the cost of the configuration at time $t$. The induction hypothesis identifies the simulated run after the earlier accumulated cost with the encoding of the original configuration at time $t$. The avoidance assumption applies at that time, so the lockstep step condition says that running the simulator for this configuration's cost reaches the encoding of its one-step successor. Combining these runs using the run-addition law (`runFrom_add`) yields the simulated run at the full accumulated cost. The original successor configuration is the run after $t+1$ steps, by the successor-run identity (`runFrom_succ_eq_step'`), giving the desired equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
