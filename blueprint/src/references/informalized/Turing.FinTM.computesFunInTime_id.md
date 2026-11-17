<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Composition.lean :: Turing.FinTM.computesFunInTime_id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity in Linear Time

**Claim.** There is a finite Turing machine that outputs each Boolean input word $x$ unchanged and halts within $c(|x|+1)$ steps for some constant $c$.

**Proof.** Choose the identity machine, which scans the input and emits each symbol as it goes, and take $c=1$. The run lemma ( `idTM_run`) says that after $|x|$ steps it is still in its scanning state, its head is just past the input, and its output is $x$. Hence it reads the end marker on the next step. The one-step run equation ( `runFrom_succ_eq_step'`) identifies that step with the machine's transition on the end marker; that transition halts without changing the already emitted output. Thus it computes $x$ in $|x|+1$ steps. This is exactly $1\cdot(|x|+1)$, so the claimed bound follows (the proof also invokes time monotonicity to pass from the computation witness to that bound).

**Key facts.** `Turing.FinTM.idTM_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.ComputesInTime.mono`.
