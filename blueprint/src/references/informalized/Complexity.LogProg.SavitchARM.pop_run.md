<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.pop_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pop Routine Execution

**Claim.** Under the stated zero-register, register-bound, and stack-decomposition hypotheses, the pop routine reaches the increment-level instruction with the endpoint stack reduced from $q2^w+e$ to $q$ and endpoint register set to $e$, while all configurations satisfy the guard.

**Proof.** The stack decomposition and $e<2^w$ imply that dividing the stack value by $2^w$ yields quotient $q$. In particular, $q$ is no larger than the original stack, which also gives the bound needed for the later shift. The routine then performs these operations in sequence, composing their guarded reachability statements using `AReach.trans`: copy the stack into scratch register $T$ (`cp_run`); copy the width into counter $C$ (`cp_run`); halve $T$ exactly $w$ times, leaving $q$ (`hv_run` and the quotient identity); copy this quotient into $Q$ and copy the width into $C$ (`cp_run` twice); shift $Q$ left by $w$ places, obtaining $q2^w$ (`sh_run`); subtract that quantity from the stack, leaving $e$ (`sb_run` and the original decomposition); and move the remainder into the endpoint register (`mv_run`). Finally, the move routines restore the scratch registers and place the machine at the increment-level instruction. The last endpoint is identified with the specified updated state by the stated register equalities, and `reach_of_eq` transports reachability across this equality. Each routine's reachability theorem supplies the guard throughout its segment.

**Key facts.** `Complexity.LogProg.SavitchARM.cp_run`, `Complexity.LogProg.SavitchARM.hv_run`, `Complexity.LogProg.SavitchARM.sh_run`, `Complexity.LogProg.SavitchARM.sb_run`, `Complexity.LogProg.SavitchARM.mv_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
