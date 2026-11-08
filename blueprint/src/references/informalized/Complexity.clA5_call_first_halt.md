<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_call_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halt in a Padded Run

**Claim.** If a live configuration reaches a halted configuration after $t$ steps, there is a first halt time $u$ with $0<u\le t$; all earlier configurations are live, and the configuration at time $u$ equals the one at time $t$.

**Proof.** Choose the least time $u$ at which the run is halted; such a time exists because time $t$ is halted. Minimality ensures every time before $u$ is live, and also gives $u\le t$. The initial configuration is live, so $u$ cannot be zero. From the run composition law (`runFrom_add`), the configuration at time $t$ is obtained by running for $t-u$ more steps from the configuration at time $u$. A halted configuration remains unchanged under further steps (`runFrom_of_halt`), so this later configuration equals the one at time $u$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
