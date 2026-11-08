<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.simTo_of_reaches -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Gives Bounded Simulation

**Claim.** If the program reaches the specified final configuration and every earlier configuration is an ordinary state with register $r$’s head at position $0$, then the run is a simulation whose earlier configurations are ordinary and whose register heads all lie between $-1$ and $W$.

**Proof.** Choose a time $T$ witnessing reachability, so the run reaches the final configuration at time $T$. For each $t<T$, reachability supplies a state $s$ and input-head position such that the configuration at time $t$ is the corresponding $xCfg$ configuration, the program has no call at $s$, and register $r$’s head is at $0$. Apply the characterization of intermediate $xCfg$ configurations (`mid_xCfg`): the head position $q=0$ satisfies $-1\le q\le W$ because $W\ge0$, so this configuration is an intermediate simulation configuration. Thus the same $T$ witnesses the required simulation.

**Key facts.** `Complexity.LogProg.mid_xCfg`.
