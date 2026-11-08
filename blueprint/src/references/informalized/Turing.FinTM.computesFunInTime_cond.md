<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.computesFunInTime_cond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Conditional Composition

**Claim.** If a decider computes $[p(x)]$ in time $T_0(|x|)$ and two machines compute $f_1,f_2$ in times $T_1,T_2$, respectively, then a finite machine computes the selected output in time a constant multiple of $T_0(n)+\max(T_1(n),T_2(n))+1$.

**Proof.** Choose the timed conditional machine. For a fixed input $x$, set $B=\max(T_1(|x|),T_2(|x|))$. The branch machine selects the machine corresponding to $p(x)$; each branch computes its output within $B$ steps, since its own time bound is at most the maximum. The branch computation equivalence ( `branchTM_computes`) formalizes this choice. The decider's run has produced the one-bit answer by time $T_0(|x|)$. The timed-start result ( `timed_start`) places the conditional machine, after a controller prefix of length $a\le 2T_0(|x|)+5$, at a configuration representing the selected branch machine's initial configuration. From there, the timed branch run lemma ( `timed_branch_run`) identifies its next $B$ steps with the branch computation. Splitting a run into a prefix and a suffix ( `runFrom_add`) therefore shows that by time $a+B$ the conditional machine has halted with the selected output. This is at most $2T_0(|x|)+5+B$, which is bounded by $5(T_0(|x|)+B+1)$. Extending a valid computation to a later time is permitted by the time monotonicity lemma ( `ComputesInTime.mono`), giving the claimed uniform bound with $c=5$.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.branchTM_computes`, `Turing.FinTM.timed_start`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.timed_branch_run`, `Turing.FinTM.computesInTime_iff`.
