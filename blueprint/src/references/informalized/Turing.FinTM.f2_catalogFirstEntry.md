<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogFirstEntry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Visit to a State

**Claim.** If every configuration in state $q$ is fixed by one step, and a run from $c$ reaches a configuration $d$ in state $q$ by time $T$, then there is a time $t\le T$ at which it reaches $d$, with no earlier configuration in state $q$.

**Proof.** Let $t$ be the least time at which the run from $c$ is in state $q$. Such a time exists because the configuration at time $T$ is $d$, whose state is $q$. By minimality, every time $j<t$ has state different from $q$, and $t\le T$. The configuration at time $t$ is fixed by one step by the hypothesis, so it is fixed by any number of steps, in particular by $T-t$ steps. The run composition law says that running for $t+(T-t)$ steps is the same as first running for $t$ steps and then for $T-t$ more (`runFrom_add`). Since $t\le T$, this total is $T$. The latter run therefore ends at the time-$t$ configuration, but also at $d$ by assumption. Hence the configuration at time $t$ is $d$, as required.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
