<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_body -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of a Counter-Loop Body

**Claim.** Under the stated assumptions, after $t$ steps the counter-loop machine has the configuration obtained from the body machine's configuration after $t$ steps, with its state redirected according to the designated state and exit. Throughout the interval, it avoids the done and escape states, keeps the counter head in the specified range, and at each time its original work-head positions agree with those of the body machine at some time up to $t$.

**Proof.** First compare the machines after one step. Since the initial body state is $a$, the counter-loop transition runs the embedded body machine and redirects its resulting state. The embedding keeps the added counter tape and its head in place. For every later positive time up to $t$, split the run into this first step and the remaining steps. The assumed intermediate-state condition ensures that at each intervening time the body machine is in a state distinct from $a$ and from the designated exit state. In precisely those states, the counter-loop transition agrees with the body transition followed by state redirection. The run-agreement theorem for machines whose transitions agree on the states encountered therefore identifies the runs at these times; the embedding run theorem identifies the embedded body configuration with the body configuration at the corresponding time. This proves the claimed configuration at time $t.

For times strictly before $t$, the intermediate-state condition also rules out both redirected terminal states, done and escape. The configuration layout for the added tape shows that its head remains at $cp$ during the body simulation, hence lies in the required interval. Finally, at each time up to $t$, the identified configuration has the body's work-head positions at that same time; choosing that time as the witness gives the asserted agreement.

**Key facts.** `Turing.counter_redirect_injective`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.embedEmitTM_runFrom`, `Turing.counter_layout`.
