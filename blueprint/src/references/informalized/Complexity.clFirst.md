<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clFirst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Visit to an Absorbing Return State

**Claim.** If a run reaches a configuration in state $ret$ within $B$ steps, begins outside state $ret$, and every configuration in state $ret$ is fixed by one step, then it first enters that state at some positive time $t\le B$, and the configuration at that time is exactly the specified finish configuration.

**Proof.** Since the run is in state $ret$ at time $B$, there is at least one time at most $B$ at which it is in that state. Let $t$ be the least such time. It is positive because the initial configuration is not in state $ret$, using the fact that a run of zero steps leaves the configuration unchanged (`Turing.MultiTapeTM.runFrom_zero`). By minimality, no earlier time is in state $ret$. At time $t$ the configuration is in state $ret$, and every such configuration is fixed by one step. Iterating this fixed-point property shows that the run remains at the time-$t$ configuration for the remaining $B-t$ steps. The iteration law for runs (`Turing.MultiTapeTM.runFrom_add`) identifies the configuration at time $B$ with this later iterate. Since the configuration at time $B$ is the given finish, the configuration at time $t$ must equal finish.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_add`.
