<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_first_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First visit to an absorbing stop state

**Claim.** If every configuration whose state satisfies the decidable predicate stop is fixed by one step, and the run from $c$ reaches a configuration $d$ in a stop state at time $T$, then it reaches $d$ at some time $t\le T$ with no stop state visited at any earlier time.

**Proof.** The run visits a stop state at time $T$, so the set of times at which it visits one is nonempty. Let $t$ be its least element. Then $t\le T$, and minimality ensures that no time $j<t$ has a stop state. The configuration at time $t$ is itself in a stop state, so the absorbing-state hypothesis says it is fixed by one step. Hence it remains unchanged for the remaining $T-t$ steps. By the run-addition law (`Turing.MultiTapeTM.runFrom_add`), the configuration at time $T=t+(T-t)$ is the result of running those remaining steps from the configuration at time $t$. It therefore equals the configuration at time $t$. Since the configuration at time $T$ is $d$, the configuration at time $t$ is also $d$, as required.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
