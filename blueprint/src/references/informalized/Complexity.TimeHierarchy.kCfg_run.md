<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.kCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted computation before halting

**Claim.** If the computation from $c$ has a present state at every time $s<t$, then after $t$ steps the clock machine from the lifted $c$ is the lift of the configuration reached by $K$ after $t$ steps.

**Proof.** Induct on $t$. At time zero, both sides are the original lifted configuration. For the successor step, the induction hypothesis identifies the clock machine's configuration after $t$ steps with the lift of $K$'s configuration then. The hypothesis ensures that this latter configuration has a present state, so one-step preservation of lifted configurations (\texttt{kCfg_step}) applies. Applying the one-step run identity (\texttt{runFrom_succ_eq_step'}) to both machines now identifies their configurations after $t+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.TimeHierarchy.kCfg_step`.
