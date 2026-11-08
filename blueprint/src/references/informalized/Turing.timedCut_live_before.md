<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_live_before -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Persistence of Liveness

**Claim.** If the interpreter has a present state after $t$ steps, then it also has a present state after any $s\le t$ steps from the same configuration.

**Proof.** Assume instead that the state at time $s$ is absent. Write $t=s+d$ for some natural number $d$. The run-composition law (`runFrom_add`) identifies the run to time $t$ with a further $d$-step run from the configuration at time $s$. A halted configuration remains unchanged under every number of steps (`runFrom_of_halt`), so the configuration at time $t$ would still have absent state, contradicting the hypothesis. Thus the state at time $s$ is present.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
