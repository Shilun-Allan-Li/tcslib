<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halting Time

**Claim.** If the run from $c_0$ is halted at time $T$, there is a time $t\le T$ when its configuration equals the one at time $T$, and it was not halted at any earlier time.

**Proof.** Choose $t$ to be the least time at which the run is halted. Since time $T$ is such a time, $t\le T$, and minimality says the run was not halted earlier. Write $T=t+r$. By the run-addition law (`Turing.MultiTapeTM.runFrom_add`), the configuration at time $T$ is obtained by running $r$ more steps from the configuration at time $t$. A halted configuration is unchanged by every subsequent step (`Turing.MultiTapeTM.runFrom_of_halt`), so this is already the configuration at time $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
