<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.SafeRun.cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a safe computation step

**Claim.** If one step takes $c$ to $c_1$, the initial state of $c$ avoids the specified state, and a run of $t$ steps from $c_1$ reaches $c'$ without an earlier visit to that state, then the run of $t+1$ steps from $c$ reaches $c'$ and also avoids that state at every strictly earlier time.

**Proof.** The one-step hypothesis identifies the run from $c$ at time one with $c_1$. By the run-addition identity (`Turing.MultiTapeTM.runFrom_add`), running for $t+1$ steps from $c$ is therefore the same as first taking that one step and then running for $t$ steps from $c_1$. The latter run reaches $c'$ by the assumed safe-run property. For safety at an earlier time $t'<t+1$, split into two cases. If $t'=0$, the configuration is $c$, whose state avoids the forbidden state by assumption. Otherwise write $t'=u+1$. The same run-addition identity identifies the configuration at time $u+1$ from $c$ with the configuration at time $u$ from $c_1$. Since $u<t$, the assumed safety of the run from $c_1$ excludes the forbidden state there as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
