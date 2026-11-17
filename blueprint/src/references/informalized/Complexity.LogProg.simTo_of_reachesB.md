<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.simTo_of_reachesB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Reachability Gives Simulation

**Claim.** If the program reaches the specified final configuration and each earlier configuration is an ordinary state with register $r$’s head between $-1$ and $L$, then the run is a simulation whose earlier configurations are ordinary and whose register heads all lie between $-1$ and $W$.

**Proof.** Choose a time $T$ witnessing bounded reachability. At each earlier time $t<T$, the hypothesis represents the configuration as an $xCfg$ configuration at some head position $q$, with no call at its state and $-1\le q\le L$. Since $L\le W$, we have $-1\le q\le W$. The intermediate-configuration criterion (`mid_xCfg`) then gives the required simulation condition, using also $W\ge0$. The original time $T$ still reaches the specified final configuration, so it witnesses the simulation.

**Key facts.** `Complexity.LogProg.mid_xCfg`.
