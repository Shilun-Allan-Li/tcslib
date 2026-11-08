<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBorrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Borrow Computation

**Claim.** Starting at the end of a prefix $v$ followed by $u$, the debit machine processes the initial false segment of $u$ in $b+1$ steps, producing the borrow result and modified word while leaving the head at $|v|+b-1$.

**Proof.** Induct on $u$, with the statement quantified over every prefix $v$. If $u$ is empty, or begins with true, the first transition already determines the borrow outcome and modified word; the one-step description of the search transition (`f2_loopBorrow_step`) gives the stated configuration. If $u$ begins with false, the first step changes that leading false to true, moves the head one cell to the right, and continues searching. Apply the induction hypothesis to the tail with the enlarged prefix $v$ followed by the new true entry. Its initial false-segment length is the tail's, so adding the first step gives exactly $b+1$ steps. The resulting tape is $v$ followed by the modified word for $u$, and the head position and outcome agree with the claimed formulas after regrouping the prefix length and the false-segment length. The successor-run identity (`runFrom_succ_eq_step`) justifies composing the initial transition with that remaining run.

**Key facts.** `Turing.FinTM.f2_loopBorrow_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
