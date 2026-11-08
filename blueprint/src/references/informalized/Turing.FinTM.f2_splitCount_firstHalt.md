<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitCount_firstHalt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First halted simulation time

**Claim.** If the source machine reaches a halted configuration $d$ in $T$ steps, then the host machine started from the corresponding counter configuration reaches the counter configuration for $d$ at some time $t\le T$.

**Proof.** Since the source run is halted at time $T$, the set of times at which it is halted is nonempty. Let $t$ be its least element. Then $t\le T$, and the source is live at every time $j<t$. The live-run simulation theorem (`f2_splitCount_run`) therefore identifies the host configuration after $t$ steps with the counter configuration associated to the source configuration at time $t$. To see that this source configuration is exactly $d$, decompose $T=t+(T-t)$. The run composition law (`runFrom_add`) says that running for $T$ steps is the same as first running for $t$ steps and then for $T-t$ more. Because the configuration at time $t$ is halted, it remains fixed for all further steps (`runFrom_of_halt`). Thus the configuration at time $t$ equals the one at time $T$, namely $d$. Substituting this into the simulation equality gives the required host run, with $t\le T$.

**Key facts.** `Turing.FinTM.f2_splitCount_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
