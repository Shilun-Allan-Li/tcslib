<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First All-Returned Time of the Counter Bank

**Claim.** There is a time at most $2W+2$ when the bank first reaches the configuration with every component in return control, and at that time its counters contain the specified selected increments with their heads at zero.

**Proof.** Write $S$ for the starting bank configuration. The simultaneous counter result gives the required final configuration at time $2W+2$ (`Complexity.clBank_finish`), and in particular the bank state then has every component in return control. Thus there is at least one time at most $2W+2$ when the bank state is the all-return state. Choose the least such time $t$; this exists by the natural-number least-element principle. By its minimality, at every earlier time the state is not the all-return state. Once reached, the all-return configuration is fixed by one step (`Complexity.clBank_idle`), and hence remains fixed for any further number of steps by iteration. Therefore the configuration at time $t$ equals the configuration at time $2W+2$. The run-addition law relates these two runs by splitting at $t$, and the time bound ensures the remaining duration is $2W+2-t$ (`Turing.MultiTapeTM.runFrom_add`). The configuration at $t$ is consequently the specified final configuration.

**Key facts.** `Complexity.clBank_finish`, `Complexity.clBank_idle`, `Turing.MultiTapeTM.runFrom_add`.
