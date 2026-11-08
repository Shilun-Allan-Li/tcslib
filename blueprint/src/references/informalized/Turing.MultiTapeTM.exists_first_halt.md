<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.MultiTapeTM.exists_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halting Configuration

**Claim.** If the configuration reached after $t$ steps is halted, then some step $u\le t$ is the first step whose configuration is halted, and the configuration at step $u$ equals the configuration at step $t$.

**Proof.** Among all natural numbers $u$ for which the configuration reached after $u$ steps is halted, choose the least one. Such a step exists because the configuration at step $t$ is halted. By minimality, every step $v<u$ is not halted, and the least step satisfies $u\le t$. A halted configuration remains unchanged under further steps, so the run from the configuration at step $u$ for $t-u$ additional steps still equals that configuration (`Turing.MultiTapeTM.runFrom_of_halt`). The run-addition identity (`Turing.MultiTapeTM.runFrom_add`) identifies those additional steps with the original run at step $t$, proving the asserted equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
