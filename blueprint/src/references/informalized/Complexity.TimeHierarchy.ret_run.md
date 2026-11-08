<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockLoop.lean :: Complexity.TimeHierarchy.ret_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Returning from the Clock Scan

**Claim.** Under the stated blank-cell and nonblank-prefix assumptions on the clock tape, the return state reaches the corresponding decrement state, with the clock head at position zero and the other configuration data unchanged, after $j+1$ steps.

**Proof.** Induct on $j$. At $j=0$, the clock head starts at $-1$, which is blank by hypothesis. The return transition therefore moves right, changes to the decrement state, and leaves the underlying configuration and tapes unchanged. The one-step run identities and the clock transition rule (`clockTM_step_some`), together with the clock-cell identification (`ctrCfg_ctr`) and the action-on-configuration rule (`ctrAction_apply`), give the claimed final configuration. For the successor case, the nonblank-prefix assumption says that cell $j$ is nonblank. Thus, from head position $j$, one return step moves left and stays in the return state, placing the head at $j-1$. The clock transition rule and `ctrAction_apply` show that this step preserves the underlying configuration and tapes. The induction hypothesis now applies at position $j-1$: its required cells below $j$ are nonblank by the original assumption. Combining the initial leftward step with those $j+1$ steps, using `runFrom_succ_eq_step`, proves the result for $j+1$.

**Key facts.** `Complexity.TimeHierarchy.clockTM_step_some`, `Complexity.TimeHierarchy.ctrCfg_ctr`, `Complexity.TimeHierarchy.ctrAction_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
