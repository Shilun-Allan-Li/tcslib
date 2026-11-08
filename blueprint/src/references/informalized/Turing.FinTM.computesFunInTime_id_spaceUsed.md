<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_id_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Computation with Bounded Space

**Claim.** There is a finite Turing machine that outputs every Boolean input unchanged within $c(|x|+1)$ steps and uses at most $c$ space at every time, for some constant $c$.

**Proof.** Use the identity machine with zero work tapes and set $c=1$. The run lemma for this machine ( `f2_idTM_run`) gives the scanning behavior: after $|x|$ steps, it is still in its scanning state, its head is past the input, and its output is $x$. One further step reads the end marker and halts without changing that output, by the one-step run equation ( `runFrom_succ_eq_step'`). This proves computation in $|x|+1=1\cdot(|x|+1)$ steps, using time monotonicity to obtain the stated computation witness. Since the machine has no work tapes, its space use at every time is zero ( `spaceUsed_zero_tapes_eq_zero`), hence at most $c$.

**Key facts.** `Turing.FinTM.f2_idTM_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.ComputesInTime.mono`, `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`.
