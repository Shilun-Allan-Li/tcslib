<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.not_halts_of_repeat_nonhalt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Repeated Nonhalting Configuration Never Halts

**Claim.** If a configuration has a nonempty state and the machine returns to it after $t+1$ steps, then every configuration reached from it has a nonempty state.

**Proof.** The return after $t+1$ steps makes the configuration periodic: for every $n$, after $n(t+1)$ steps the run is back at the starting configuration. This follows by viewing the run as repeated iteration of the $(t+1)$-step map and using that this map fixes the configuration. Suppose, toward a contradiction, that the run is halted at some time $t'$. Since $t'\le t'(t+1)$, the later time can be written as $t'$ plus a nonnegative number of steps. A halted configuration remains unchanged under further steps, so the run is still halted at time $t'(t+1)$; this uses the run-addition identity (`Turing.MultiTapeTM.runFrom_add`). But periodicity says that this configuration is the original one, whose state is nonempty. This contradiction proves that no time $t'$ is halting.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
