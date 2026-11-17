<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.avoid_of_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Avoiding Halt-Forcing States

**Claim.** If the run is still live after $T$ steps, then at every time $t<T$ its state cannot satisfy $X$.

**Proof.** Fix $t<T$ and suppose the machine is in state $q$ satisfying $X$. The hypothesis says its next step halts, so the run at time $t+1$ is halted (`runFrom_succ_eq_step'`). Decompose $T=(t+1)+(T-(t+1))$. By the run addition law and the fact that a halted configuration remains unchanged (`runFrom_add`, `runFrom_of_halt`), the run at time $T$ is also halted. This contradicts the assumption that it is live at time $T$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
