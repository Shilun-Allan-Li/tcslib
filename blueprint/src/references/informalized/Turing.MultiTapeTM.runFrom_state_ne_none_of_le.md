<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.runFrom_state_ne_none_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting persists backward along a run

**Claim.** If the configuration at time $t$ is not halted, then no configuration at an earlier time $u\leq t$ is halted.

**Proof.** Fix $u\leq t$ and suppose, for contradiction, that the configuration at time $u$ is halted. Decompose the run at time $t$ into the first $u$ steps followed by $t-u$ further steps, using $t=u+(t-u)$ and `runFrom_add`. Since the configuration at time $u$ is halted, `runFrom_of_halt` says those further steps leave it unchanged. Therefore the configuration at time $t$ equals the one at time $u$, so its state is absent, contradicting the hypothesis that the state at time $t$ is not absent.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
