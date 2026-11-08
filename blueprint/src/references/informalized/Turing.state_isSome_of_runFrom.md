<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.state_isSome_of_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Earlier Configurations Have States

**Claim.** If the configuration reached after $t$ steps has state $q_f$, then every configuration reached after $j\le t$ steps has some state.

**Proof.** Fix $j\le t$ and inspect the state at time $j$. If it is some state $q$, the conclusion holds immediately. Otherwise it is none, so the machine is halted at time $j$. Write $t=j+u$ for a nonnegative number of further steps. Runs split across successive time intervals (`Turing.MultiTapeTM.runFrom_add`), and a run begun in a halted configuration remains that configuration (`Turing.runFrom_of_halted`). Hence the configuration at time $t$ equals the one at time $j$ and has state none. This contradicts the hypothesis that its state is $q_f$, which is some state. Therefore the state at time $j$ must be some state.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.runFrom_of_halted`.
