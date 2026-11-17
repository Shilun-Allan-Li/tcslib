<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_live_before -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Persistence of Liveness

**Claim.** If a machine's configuration after $t$ steps has not halted and $s\le t$, then its configuration after $s$ steps has not halted.

**Proof.** Suppose instead that the configuration at time $s$ is halted. Write $t=s+d$ for some natural number $d$. By the run-addition law (Turing.MultiTapeTM.runFrom_add), the configuration at time $t$ is obtained by running for $d$ more steps from the configuration at time $s$. A halted configuration remains unchanged under every further run (Turing.MultiTapeTM.runFrom_halt), so the configuration at time $t$ would also be halted, contrary to the hypothesis.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_halt`.
