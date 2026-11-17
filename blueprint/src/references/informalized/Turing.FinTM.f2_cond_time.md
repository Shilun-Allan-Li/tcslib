<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_cond_time -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional computation time

**Claim.** If $D$ decides $p$ with output $[p(x)]$ in time $T_0(|x|)$, and $M_1,M_2$ compute $f_1,f_2$ in times $T_1(|x|),T_2(|x|)$, then the conditional machine computes the selected function in exactly $5(T_0(|x|)+\max(T_1(|x|),T_2(|x|))+1)$ steps.

**Proof.** Fix $x$ and put $B=\max(T_1(|x|),T_2(|x|))$. The branch-machine computation theorem (\texttt{Turing.FinTM.branchTM_computes}) identifies the selected branch with the appropriate original machine. By monotonicity of computation time (\texttt{Turing.FinTM.ComputesInTime.mono}), that branch computes the selected output in exactly $B$ steps, since its own time bound is at most $B$. The timed-start lemma (\texttt{Turing.FinTM.f2_timed_start}) provides a time $a\le 2T_0(|x|)+5$ at which the conditional machine has entered a configuration representing the selected branch at its initial configuration. From then on it simulates that branch, as stated by \texttt{Turing.FinTM.f2_timed_branch_run}. The computation characterization (\texttt{Turing.FinTM.computesInTime_iff}) therefore shows that after a further $B$ steps it is halted with the selected output. This gives a computation at time $a+B$. Since $a+B\le 2T_0(|x|)+5+B\le 5(T_0(|x|)+B+1)$, monotonicity extends it to the claimed time.

**Key facts.** `Turing.FinTM.branchTM_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_timed_start`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_timed_branch_run`, `Turing.FinTM.computesInTime_iff`.
