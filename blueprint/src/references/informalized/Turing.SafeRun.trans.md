<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.SafeRun.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Safe Runs

**Claim.** If the machine runs safely from $c$ to $c_1$ in $t_1$ steps and safely from $c_1$ to $c'$ in $t_2$ steps, then it runs safely from $c$ to $c'$ in $t_1+t_2$ steps.

**Proof.** The run-composition identity says that running for $t_1+t_2$ steps from $c$ is the same as running for $t_2$ steps from the configuration reached after $t_1$ steps (`Turing.MultiTapeTM.runFrom_add`). Since the first run ends at $c_1$ and the second at $c'$, this gives the required endpoint. For safety, take any time $t'<t_1+t_2$. If $t'<t_1$, the first run's safety condition excludes the avoided state. Otherwise write $t'=t_1+u$ for some natural number $u$. The run-composition identity identifies the configuration at that time with the configuration reached after $u$ steps from $c_1$. The bound on $t'$ gives $u<t_2$, so the second run's safety condition excludes the avoided state there as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
