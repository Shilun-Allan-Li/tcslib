<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_cycle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact macrostep duration

**Claim.** Starting at the macrostep-check phase with unary head at $u$ and guide head at $0$, the schedule machine returns to that phase after $6R+8$ steps, with unary head at $u+1$ and guide head at $0$.

**Proof.** The first check step sees the unit marker at $u$, so it enters the leftward-seek phase (`macroCfg_check`). The seek takes $R+2$ steps to reach the left edge at $-R-1$ and enter the forward phase (`macroCfg_seek_run`, `macroCfg_seek`). The forward scan then takes $2R+2$ steps to reach the right edge at $R+1$ and enter the backward phase (`macroCfg_forward_run`, `macroCfg_forward`). The backward scan takes another $2R+2$ steps to reach the left edge and enter the return-to-center phase (`macroCfg_backward_run`, `macroCfg_backward`). Finally, returning from $-R$ to the origin takes $R+1$ steps; there the machine enters macrostep-check, advances the unary head to $u+1$, and leaves the guide head at $0$ (`macroCfg_center_run`, `macroCfg_center`). These segments concatenate because running for $a+b$ steps is running for $a$ steps and then $b$ more (`runFrom_add`). Their total is $1+(R+2)+(2R+2)+(2R+2)+(R+1)=6R+8$.

**Key facts.** `Complexity.macroCfg_check`, `Complexity.macroCfg_seek_run`, `Complexity.macroCfg_seek`, `Complexity.macroCfg_forward_run`, `Complexity.macroCfg_forward`, `Complexity.macroCfg_backward_run`, `Complexity.macroCfg_backward`, `Complexity.macroCfg_center_run`, `Complexity.macroCfg_center`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
