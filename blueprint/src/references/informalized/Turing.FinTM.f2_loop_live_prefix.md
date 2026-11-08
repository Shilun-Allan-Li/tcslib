<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loop_live_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting Throughout a Run Prefix

**Claim.** If the machine is still in a state after $t$ steps, then it is still in a state after every $u\le t$ steps.

**Proof.** Fix $u\le t$ and suppose, for contradiction, that the run at time $u$ is halted. Decompose the run at time $t$ into its first $u$ steps and the remaining $t-u$ steps (`Turing.MultiTapeTM.runFrom_add`). Since a halted configuration remains unchanged under further steps (`Turing.MultiTapeTM.runFrom_of_halt`), the configuration at time $t$ would then equal the halted configuration at time $u$. This contradicts the assumption that the run at time $t$ is not halted.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
